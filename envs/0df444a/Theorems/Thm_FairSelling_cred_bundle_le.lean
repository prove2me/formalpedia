-- Prove2me | Theorems.Thm_FairSelling_cred_bundle_le
-- name    : FairSelling.cred_bundle_le
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:13:28.957567+00:00
-- url     : https://prove2.me/theorems/dabf7502-03b7-45d3-9d03-089a98912131
-- title:
--   Fair Selling: cred bundle le
-- statement:
--   The credits of the events charged to a single bundle are covered by the value that the bundle
--   has lost, up to `ε` per event.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsDescent.lean#L66-L107
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsDescent.lean#L66-L107

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
omit [Fintype G] [DecidableEq κ]

theorem FairSelling.cred_bundle_le (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {ε : ℝ}
    (bg : ι → Finset G) (wit : κ → G) (bidx : κ → ι) (cred : κ → ℝ)
    {R : Finset G} {Q : Finset κ}
    (hwit_mem : ∀ b ∈ Q, wit b ∈ bg (bidx b))
    (hcred_wit : ∀ b ∈ Q, cred b ≤ vbar w p (wit b) + ε)
    (hbval : ∀ j, vbarSum w p (bg j) ≤ 3 * ε)
    (hwit_out : ∀ b ∈ Q, wit b ∉ R)
    (hinj : Set.InjOn wit ↑Q) (j : ι) :
    ∑ b ∈ Q.filter (fun b => bidx b = j), cred b
      ≤ (3 * ε - vbarSum w p (bg j ∩ R))
          + ((Q.filter (fun b => bidx b = j)).card : ℝ) * ε := by sorry
