-- Prove2me | Theorems.Thm_FairSelling_ratio_TPS_le_MMS
-- name    : FairSelling.ratio_TPS_le_MMS
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:37:35.919583+00:00
-- url     : https://prove2.me/theorems/be1a8a9b-8589-4b93-8e16-1eb251a4e9d1
-- title:
--   Fair Selling: ratio TPS le MMS
-- statement:
--   Applying the `n/(2n−1)`-TPS approximation to `n` copies of a single agent shows that the
--   maximin share with selling is at least `n/(2n−1)` of the truncated proportional share.  (By
--   Lemma 1 the two shares satisfy `MMS ≤ TPS`; this is a converse bound.)
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefx.lean#L251-L255
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TPSSefx.lean#L251-L255

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EpsEnvy
import Definitions.Def_RequestProject_LemmaEleven
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSSefx
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.ratio_TPS_le_MMS (v p : G → ℝ) (hn : 0 < n) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g) :
    ((n : ℝ) / (2 * n - 1)) * TPS n v p ≤ MMS n v p := by sorry
