-- Prove2me | Theorems.Thm_FairSelling_fill_one
-- name    : FairSelling.fill_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T01:46:42.293889+00:00
-- url     : https://prove2.me/theorems/10470c40-f9dc-486c-b54e-6ba8ad2b979f
-- title:
--   Fair Selling: fill one
-- statement:
--   The last step of the filling procedure: a single part, the special one, which simply absorbs
--   all the remaining resources.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsProp6.lean#L277-L386
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsProp6.lean#L277-L386

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_TwoThirdsCanonical
import Definitions.Def_RequestProject_TwoThirdsBagFilling
import Definitions.Def_RequestProject_TwoThirdsProp6
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G]
omit [Fintype G]

theorem FairSelling.fill_one (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {ε : ℝ} (hε : 0 ≤ ε)
    (A C S : Finset G) (d r : ℝ) (f₀ : Option G)
    (hS2 : ∀ g ∈ S, vbar w p g = p g)
    (hAC : Disjoint A C) (hAS : Disjoint A S) (hCS : Disjoint C S)
    (hd : 0 ≤ d) (hr : r = 0 ∨ ε ≤ r)
    (hf₀ : ∀ f, f₀ = some f → f ∉ A ∧ f ∉ C ∧ f ∉ S ∧ r ≤ p f ∧ ε ≤ p f)
    (hf₀n : f₀ = none → r = 0)
    (hbud : 2 * ε ≤ (∑ g ∈ A, vbar w p g) + (∑ g ∈ C, vbar w p g) + d + (∑ g ∈ S, p g) + r) :
    Nonempty (FillOut w p ε 1 (A ∪ C ∪ S) d r f₀) := by sorry
