-- Prove2me | Theorems.Thm_FairSelling_canonical_strict_two_pure
-- name    : FairSelling.canonical_strict_two_pure
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:07:46.303256+00:00
-- url     : https://prove2.me/theorems/d2a6e033-3a48-4da9-a309-4bdc252f1b3a
-- title:
--   Fair Selling: canonical strict two pure
-- statement:
--   **The two-pure-bundles case.**  If every good other than `F` is worth less than `(2/3)·τ`,
--   greedy bag-filling produces two pure bundles and a leftovers bundle containing `F`; nothing is
--   sold.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/CanonicalStrict.lean#L220-L278
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/CanonicalStrict.lean#L220-L278

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_CanonicalStrict
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.canonical_strict_two_pure (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {τ : ℝ} (hτ : 0 < τ) (F : G)
    (hsmall : ∀ g ∈ (Finset.univ \ ({F} : Finset G)), vbar w p g < (2 / 3) * τ)
    (htot3 : 3 * τ ≤ vbarSum w p (Finset.univ \ {F}))
    (htotall : 4 * τ ≤ vbarSum w p Finset.univ) :
    ∃ (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (leftover : Fin 3),
      IsCanonicalStrict w p τ kept sold money leftover := by sorry
