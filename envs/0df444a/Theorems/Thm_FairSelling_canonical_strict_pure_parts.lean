-- Prove2me | Theorems.Thm_FairSelling_canonical_strict_pure_parts
-- name    : FairSelling.canonical_strict_pure_parts
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:07:25.296268+00:00
-- url     : https://prove2.me/theorems/0ee45270-2563-4a08-8578-9ede0861f13b
-- title:
--   Fair Selling: canonical strict pure parts
-- statement:
--   **The manuscript's easy case.**  If at most one part of an MMS configuration carries more than
--   `r - τ` in sale proceeds, that part becomes the leftovers bundle and the two other parts become
--   pure.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/CanonicalStrict.lean#L59-L82
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/CanonicalStrict.lean#L59-L82

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_CanonicalStrict
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G] [DecidableEq G]

theorem FairSelling.canonical_strict_pure_parts (w p : G → ℝ) {τ r : ℝ}
    (A : Fin 3 → Finset G) (s : Finset G) (q : Fin 3 → ℝ)
    (hdisjA : ∀ i j, i ≠ j → Disjoint (A i) (A j)) (hdisjs : ∀ i, Disjoint s (A i))
    (hq0 : ∀ i, 0 ≤ q i) (hqsum : ∑ i, q i = ∑ g ∈ s, p g)
    (hge : ∀ i, r ≤ vbarSum w p (A i) + q i) (hscard : s.card ≤ 2)
    (lo : Fin 3) (hsmallq : ∀ i, i ≠ lo → q i ≤ r - τ) (hτr : τ ≤ r) :
    ∃ (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (leftover : Fin 3),
      IsCanonicalStrict w p τ kept sold money leftover := by sorry
