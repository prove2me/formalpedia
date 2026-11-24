-- Prove2me | Theorems.Thm_FairSelling_exists_twothirds_MMS
-- name    : FairSelling.exists_twothirds_MMS
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:14:24.691419+00:00
-- url     : https://prove2.me/theorems/34025237-bd6c-4a91-8d1b-0512e6c30180
-- title:
--   Fair Selling: exists twothirds MMS
-- statement:
--   **Theorem 3 (general `n`).**  Every allocation instance with optional selling admits a valid
--   outcome giving every agent at least `2/3` of its maximin share.
--
--   (For `n = 3` the stronger `3/4` bound of `exists_threequarter_MMS_three` is available, and for
--   `n = 2` the exact maximin share is achievable, `exists_MMS_two`.)
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirds.lean#L193-L207
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirds.lean#L193-L207

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsLoss
import Definitions.Def_RequestProject_TwoThirdsLemma9
import Definitions.Def_RequestProject_TwoThirds
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.exists_twothirds_MMS (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g) :
    ∃ o : Outcome G n, o.Valid p ∧ ∀ i, (2 / 3 : ℝ) * MMS n (v i) p ≤ util (v i) o i := by sorry
