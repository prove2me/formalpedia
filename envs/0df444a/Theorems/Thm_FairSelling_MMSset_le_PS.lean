-- Prove2me | Theorems.Thm_FairSelling_MMSset_le_PS
-- name    : FairSelling.MMSset_le_PS
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T01:37:14.047656+00:00
-- url     : https://prove2.me/theorems/eab6eb8d-ea03-4409-8247-14f54d53f7fa
-- title:
--   Fair Selling: MMSset le PS
-- statement:
--   Every value guaranteeable by a valid outcome is at most the proportional share.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceeds.lean#L63-L68
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/EqualProceeds.lean#L63-L68

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_EqualProceeds
set_option autoImplicit true
open scoped BigOperators
open FairSelling
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.MMSset_le_PS (v p : G → ℝ) (hn : 0 < n) (hv : ∀ g, 0 ≤ v g) (hp : ∀ g, 0 ≤ p g)
    {r : ℝ} (hr : r ∈ MMSset n v p) : r ≤ PS n v p := by sorry
