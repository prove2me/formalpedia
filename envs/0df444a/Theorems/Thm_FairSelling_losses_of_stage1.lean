-- Prove2me | Theorems.Thm_FairSelling_losses_of_stage1
-- name    : FairSelling.losses_of_stage1
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:11:16.2962+00:00
-- url     : https://prove2.me/theorems/b77ef6ad-ae41-4cb3-bb2c-aaa5c6e63a2a
-- title:
--   Fair Selling: losses of stage1
-- statement:
--   **Proposition 5, first stage of the preliminary phase.**  Selling an expensive good `g` and
--   paying its threshold to the active agent `j` of *lowest* maximin share preserves the accounting:
--   for a remaining active agent this is a loss of type `ℓ₁` (if it did not intend to sell `g`) or of
--   type `ℓ₂` (if it did).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsLoss.lean#L468-L492
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsLoss.lean#L468-L492

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_ThreeAgents
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_EquiMMS
import Definitions.Def_RequestProject_TwoThirdsLoss
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.losses_of_stage1 (v : Fin n → G → ℝ) (p : G → ℝ) {T : Finset (Fin n)} {R : Finset G}
    {D : ℝ} (hL : Losses v p T R D)
    {j : Fin n} (hj : j ∈ T) (hmin : ∀ a ∈ T, MMS n (v j) p ≤ MMS n (v a) p)
    {g : G} (hg : g ∈ R) (hprice : thr v p j ≤ p g) (hthr0 : 0 ≤ thr v p j) :
    Losses v p (T.erase j) (R.erase g) (D + p g - thr v p j) := by sorry
