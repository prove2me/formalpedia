-- Prove2me | Theorems.Thm_FairSelling_canonical_partition_three_strict
-- name    : FairSelling.canonical_partition_three_strict
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:08:06.094431+00:00
-- url     : https://prove2.me/theorems/4bf9ade9-a3ab-493d-898f-030015c0b836
-- title:
--   Fair Selling: canonical partition three strict
-- statement:
--   **Lemma 3, strict form.**  For a single agent with additive non-negative valuation `w` and
--   non-negative prices `p`, if every good is small (`v̄(g) < 3/4 · MMS`), then the goods admit a
--   *strictly* canonical partition into three bundles, each of value at least `3/4 · MMS`: at most two
--   goods are force-sold, each non-leftovers bundle is pure or a single good topped up with money from
--   the sale of a single good `f` with `p f ≥ MMS / 4`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/CanonicalStrict.lean#L285-L408
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/CanonicalStrict.lean#L285-L408

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_CanonicalStrict
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.canonical_partition_three_strict (w p : G → ℝ) (hw : ∀ g, 0 ≤ w g) (hp : ∀ g, 0 ≤ p g)
    (hsmall : ∀ g, vbar w p g < (3 / 4) * MMS 3 w p) :
    ∃ (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (leftover : Fin 3),
      IsCanonicalStrict w p ((3 / 4) * MMS 3 w p) kept sold money leftover := by sorry
