-- Prove2me | Theorems.Thm_FairSelling_canonical_items_money
-- name    : FairSelling.canonical_items_money
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:05:17.984798+00:00
-- url     : https://prove2.me/theorems/12a92a80-807a-4218-9347-c7d10de21c7d
-- title:
--   Fair Selling: canonical items money
-- statement:
--   The Fair Selling construction uses the canonical items money property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/CanonicalPartition.lean#L154-L254
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/CanonicalPartition.lean#L154-L254

import Mathlib
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_Matching
import Definitions.Def_RequestProject_MMSPartition
import Definitions.Def_RequestProject_CanonicalPartition
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
set_option maxHeartbeats 1600000

theorem FairSelling.canonical_items_money (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (hsmall : ∀ g, vbar w p g < (3/4) * MMS 3 w p) (s : Finset G) (hscard : s.card ≤ 2)
    (hP : (2/3) * ((3/4) * MMS 3 w p) < ∑ g ∈ s, p g)
    (hV : 4 * ((3/4) * MMS 3 w p) ≤ vbarSum w p (Finset.univ \ s) + ∑ g ∈ s, p g) :
    ∃ (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (leftover : Fin 3),
      IsCanonical w p ((3/4) * MMS 3 w p) kept sold money leftover := by sorry
