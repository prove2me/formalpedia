-- Prove2me | Theorems.Thm_FairSelling_exists_twothirds_MMS_of_equiMMS
-- name    : FairSelling.exists_twothirds_MMS_of_equiMMS
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:14:34.759141+00:00
-- url     : https://prove2.me/theorems/713dfb55-93a0-4158-bdfa-c605c5ec52e6
-- title:
--   Fair Selling: exists twothirds MMS of equi MMS
-- statement:
--   **Theorem 3 (general `n`), for instances in which every agent has an equi-valued MMS
--   partition.**  Every such instance admits a valid outcome giving every agent at least `2/3` of its
--   maximin share.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirds.lean#L173-L186
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirds.lean#L173-L186

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

theorem FairSelling.exists_twothirds_MMS_of_equiMMS (v : Fin n → G → ℝ) (p : G → ℝ) (hn : 0 < n)
    (hv : ∀ i g, 0 ≤ v i g) (hp : ∀ g, 0 ≤ p g)
    (hE : ∀ i, Nonempty (EquiMMS (v i) p (MMS n (v i) p) n)) :
    ∃ o : Outcome G n, o.Valid p ∧ ∀ i, (2 / 3 : ℝ) * MMS n (v i) p ≤ util (v i) o i := by sorry
