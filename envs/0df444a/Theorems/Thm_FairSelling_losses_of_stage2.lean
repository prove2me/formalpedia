-- Prove2me | Theorems.Thm_FairSelling_losses_of_stage2
-- name    : FairSelling.losses_of_stage2
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:11:13.325388+00:00
-- url     : https://prove2.me/theorems/47c70470-5d1d-46e2-8042-e462703c7f44
-- title:
--   Fair Selling: losses of stage2
-- statement:
--   **Proposition 5, second stage of the preliminary phase.**  Handing a good `g` that agent `i`
--   values above its threshold to `i` preserves the accounting: for a remaining active agent this is a
--   loss of type `ℓ₁` (if it did not intend to sell `g`) or of type `ℓ₂` (if it did — and then its
--   `v̄` value of `g` is its price, which the first stage has left below the threshold).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsLoss.lean#L498-L520
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsLoss.lean#L498-L520

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

theorem FairSelling.losses_of_stage2 (v : Fin n → G → ℝ) (p : G → ℝ) {T : Finset (Fin n)} {R : Finset G}
    {D : ℝ} (hL : Losses v p T R D)
    (hstage1 : ∀ a ∈ T, ∀ e ∈ R, p e < thr v p a)
    {i : Fin n} (hi : i ∈ T) {g : G} (hg : g ∈ R) :
    Losses v p (T.erase i) (R.erase g) D := by sorry
