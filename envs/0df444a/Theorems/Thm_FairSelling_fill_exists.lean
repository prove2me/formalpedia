-- Prove2me | Theorems.Thm_FairSelling_fill_exists
-- name    : FairSelling.fill_exists
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-24T02:12:12.514642+00:00
-- url     : https://prove2.me/theorems/a6e5928b-be4c-4cdd-996f-23a84e6336af
-- title:
--   Fair Selling: fill exists
-- statement:
--   **The filling procedure.**  `m + 1` parts, the special one being part `0`, are built out of
--   the large goods `A`, the cheap goods `C`, the goods `S` that the agent intends to sell, the
--   banked money `d` and the proceeds `r` of the good `f₀` currently being sold.
--
--   The two structural hypotheses are that there are no more large goods than parts (`A.card ≤ m+1`)
--   and that, unless there is nothing left to sell, every part gets a large good
--   (`A.card = m+1 ∨ (S = ∅ ∧ r = 0)`); the quantitative hypothesis is that the total value at our
--   disposal is at least `m·μ + t`, i.e. `μ` for each of the `m` non-special parts and `t` for the
--   special one, where `μ = 3ε` and `t = 2ε`.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsProp6.lean#L397-L732
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsProp6.lean#L397-L732

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

theorem FairSelling.fill_exists (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ (m : ℕ) (A C S : Finset G) (d r : ℝ) (f₀ : Option G),
      (∀ g ∈ A, ε ≤ vbar w p g) → (∀ g ∈ A, vbar w p g ≤ 2 * ε) →
      (∀ g ∈ C, vbar w p g ≤ ε) →
      (∀ g ∈ S, ε ≤ p g) → (∀ g ∈ S, vbar w p g = p g) →
      Disjoint A C → Disjoint A S → Disjoint C S →
      0 ≤ d → (r = 0 ∨ ε ≤ r) →
      (∀ f, f₀ = some f → f ∉ A ∧ f ∉ C ∧ f ∉ S ∧ r ≤ p f ∧ ε ≤ p f) →
      (f₀ = none → r = 0) →
      A.card ≤ m + 1 → (A.card = m + 1 ∨ (S = ∅ ∧ r = 0)) →
      (m : ℝ) * (3 * ε) + 2 * ε
        ≤ (∑ g ∈ A, vbar w p g) + (∑ g ∈ C, vbar w p g) + d + (∑ g ∈ S, p g) + r →
      Nonempty (FillOut w p ε (m + 1) (A ∪ C ∪ S) d r f₀) := by sorry
