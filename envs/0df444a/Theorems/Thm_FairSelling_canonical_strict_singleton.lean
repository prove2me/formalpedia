-- Prove2me | Theorems.Thm_FairSelling_canonical_strict_singleton
-- name    : FairSelling.canonical_strict_singleton
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:07:26.30668+00:00
-- url     : https://prove2.me/theorems/0e68ec6e-fd12-431d-8ff1-36febbe908c4
-- title:
--   Fair Selling: canonical strict singleton
-- statement:
--   **The singleton case.**  A good `e` that can be topped up with proceeds from the expensive
--   force-sold good `F` to exactly `τ` yields a strictly canonical partition: the singleton bundle
--   `{e}`, a bag-filled pure bundle, and the leftovers.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/CanonicalStrict.lean#L87-L215
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/CanonicalStrict.lean#L87-L215

import Mathlib
import Definitions.Def_RequestProject_CanonicalPartition
import Definitions.Def_RequestProject_MatchingPhase
import Definitions.Def_RequestProject_CanonicalStrict
set_option autoImplicit true
open scoped BigOperators
set_option maxHeartbeats 1000000
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G]

theorem FairSelling.canonical_strict_singleton (w p : G → ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hsmall : ∀ g, vbar w p g < τ) (F e : G) (heF : e ≠ F)
    (hpF : τ / 3 ≤ p F)
    (htop : τ ≤ vbar w p e + p F)
    (htot : 4 * τ ≤ vbarSum w p (Finset.univ \ {F}) + p F) :
    ∃ (kept : Fin 3 → Finset G) (sold : Finset G) (money : Fin 3 → ℝ) (leftover : Fin 3),
      IsCanonicalStrict w p τ kept sold money leftover := by sorry
