-- Prove2me | Theorems.Thm_FairSelling_canonical_strict_trivial
-- name    : FairSelling.canonical_strict_trivial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:07:10.051224+00:00
-- url     : https://prove2.me/theorems/e8b8841d-e721-4633-a9d7-ef3440dbfdbf
-- title:
--   Fair Selling: canonical strict trivial
-- statement:
--   The degenerate case `τ ≤ 0`: the empty partition is strictly canonical.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/CanonicalStrict.lean#L47-L53
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/CanonicalStrict.lean#L47-L53

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

theorem FairSelling.canonical_strict_trivial (w p : G → ℝ) {τ : ℝ} (hτ : τ ≤ 0) :
    ∃ (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (leftover : Fin 3),
      IsCanonicalStrict w p τ kept sold money leftover := by sorry
