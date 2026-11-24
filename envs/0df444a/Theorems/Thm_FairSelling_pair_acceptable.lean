-- Prove2me | Theorems.Thm_FairSelling_pair_acceptable
-- name    : FairSelling.pair_acceptable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:13:46.977156+00:00
-- url     : https://prove2.me/theorems/a961df61-aa6d-47fa-a441-ef80df098238
-- title:
--   Fair Selling: pair acceptable
-- statement:
--   Each of the two goods of a pure part made of two large goods is worth at least `ε`, so the
--   part is acceptable.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsDescent.lean#L112-L116
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsDescent.lean#L112-L116

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsProp6
import Definitions.Def_RequestProject_TwoThirdsGlue
import Definitions.Def_RequestProject_TwoThirdsDescent
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G]
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]
omit [Fintype G]

theorem FairSelling.pair_acceptable (w p : G → ℝ) {ε : ℝ} {d₁ d₂ : G} (hne : d₁ ≠ d₂)
    (h₁ : ε ≤ vbar w p d₁) (h₂ : ε ≤ vbar w p d₂) :
    2 * ε ≤ vbarSum w p {d₁, d₂} := by sorry
