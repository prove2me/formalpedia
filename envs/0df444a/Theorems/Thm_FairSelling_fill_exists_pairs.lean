-- Prove2me | Theorems.Thm_FairSelling_fill_exists_pairs
-- name    : FairSelling.fill_exists_pairs
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:12:31.657152+00:00
-- url     : https://prove2.me/theorems/4d93094e-afdb-4c69-a7d9-8d2f0706b5e6
-- title:
--   Fair Selling: fill exists pairs
-- statement:
--   **The filling procedure with pairing.**  If there are `t` large goods in excess of the number
--   of parts, `t` of the parts are made of *two* large goods each: such a part is pure and acceptable,
--   since a large good is worth at least `ε`.  Each such part may cost as much as `4ε` — more than the
--   `μ = 3ε` a part is allowed in the accounting of `fill_exists` — which is why the hypothesis asks
--   for `t·ε` of extra value.  This is the manuscript's step "if `|L₀| ≥ 2n₀` … create
--   `t = |L₀| − n₀ − 1` acceptable pure bundles, each containing two goods from `L₀`".
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsProp6.lean#L742-L865
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsProp6.lean#L742-L865

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

theorem FairSelling.fill_exists_pairs (w p : G → ℝ) (hp : ∀ g, 0 ≤ p g) {ε : ℝ} (hε : 0 ≤ ε) :
    ∀ (t m : ℕ) (A C S : Finset G) (d r : ℝ) (f₀ : Option G),
      (∀ g ∈ A, ε ≤ vbar w p g) → (∀ g ∈ A, vbar w p g ≤ 2 * ε) →
      (∀ g ∈ C, vbar w p g ≤ ε) →
      (∀ g ∈ S, ε ≤ p g) → (∀ g ∈ S, vbar w p g = p g) →
      Disjoint A C → Disjoint A S → Disjoint C S →
      0 ≤ d → (r = 0 ∨ ε ≤ r) →
      (∀ f, f₀ = some f → f ∉ A ∧ f ∉ C ∧ f ∉ S ∧ r ≤ p f ∧ ε ≤ p f) →
      (f₀ = none → r = 0) →
      A.card ≤ m + 1 + t → (A.card = m + 1 + t ∨ (S = ∅ ∧ r = 0)) →
      (m : ℝ) * (3 * ε) + 2 * ε + (t : ℝ) * ε
        ≤ (∑ g ∈ A, vbar w p g) + (∑ g ∈ C, vbar w p g) + d + (∑ g ∈ S, p g) + r →
      Nonempty (FillOut w p ε (m + 1) (A ∪ C ∪ S) d r f₀) := by sorry
