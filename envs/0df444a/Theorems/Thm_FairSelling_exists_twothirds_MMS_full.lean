-- Prove2me | Theorems.Thm_FairSelling_exists_twothirds_MMS_full
-- name    : FairSelling.exists_twothirds_MMS_full
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T03:16:57.02145+00:00
-- url     : https://prove2.me/theorems/95e824a4-e320-4804-81f9-d9565b1dacdf
-- title:
--   Fair Selling: exists twothirds MMS full
-- statement:
--   **Theorem 3 (general `n`), full-allocation form.**  Every allocation instance with optional
--   selling admits a *full* allocation — every good is either sold or handed to an agent, and the
--   sale proceeds are distributed in full — giving every agent at least `2/3` of its maximin share.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsFull.lean#L128-L134
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsFull.lean#L128-L134

import Mathlib
import Definitions.Def_RequestProject_TwoThirds
import Definitions.Def_RequestProject_LemmaTen
import Definitions.Def_RequestProject_TwoThirdsFull
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.exists_twothirds_MMS_full (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Full p Finset.univ ∧
      ∀ i, (2 / 3 : ℝ) * MMS n (v i) p ≤ util (v i) o i := by sorry
