-- Prove2me | Theorems.Thm_FairSelling_canonical_partition_three_small
-- name    : FairSelling.canonical_partition_three_small
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:56:21.988812+00:00
-- url     : https://prove2.me/theorems/4bce356f-207f-46aa-9ece-de2dcbebc8c8
-- title:
--   Fair Selling: canonical partition three small
-- statement:
--   The Fair Selling construction uses the canonical partition three small property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/CanonicalPartition.lean#L116-L141
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/CanonicalPartition.lean#L116-L141

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_CanonicalPartition
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.canonical_partition_three_small (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (hsmall : ∀ g, vbar w p g < (1/2) * MMS 3 w p) :
    ∃ (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (leftover : Fin 3),
      IsCanonical w p ((3/4) * MMS 3 w p) kept sold money leftover := by sorry
