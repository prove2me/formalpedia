-- Prove2me | Theorems.Thm_FairSelling_canonical_of_inv
-- name    : FairSelling.canonical_of_inv
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:14:24.865894+00:00
-- url     : https://prove2.me/theorems/869d6c5f-a341-4696-994f-0bdc5a35e1c8
-- title:
--   Fair Selling: canonical of inv
-- statement:
--   **Lemma 9.**  For `ρ = 2/3`, a canonical partition exists at every step of the main part of
--   the algorithm: the active agent `i` of highest maximin share can partition the available goods and
--   money into `|T|` parts that are all acceptable to it and that satisfy the three canonicity
--   conditions.
--
--   The hypothesis `hmax` (agent `i` has the largest maximin share among the active agents) is the
--   one the manuscript states; the formal proof does not use it, because the consequence the
--   manuscript draws from it — the lower bound `μ − t ≤ p f` on the price of a good sold in a round —
--   is already part of the definition of the loss types `ℓ₃` and `ℓ₄` (see `LossL3`).
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsLemma9.lean#L38-L202
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsLemma9.lean#L38-L202

import Mathlib
import Definitions.Def_RequestProject_TwoThirdsBudget
import Definitions.Def_RequestProject_TwoThirdsDescent
import Definitions.Def_RequestProject_TwoThirdsLemma9
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}

theorem FairSelling.canonical_of_inv (v : Fin n → G → ℝ) (p : G → ℝ) (hv : ∀ i g, 0 ≤ v i g)
    (hp : ∀ g, 0 ≤ p g) {T : Finset (Fin n)} {R : Finset G} {D : ℝ} (hInv : Inv v p T R D)
    {i : Fin n} (hi : i ∈ T) (hmax : ∀ a ∈ T, MMS n (v a) p ≤ MMS n (v i) p)
    {k : ℕ} [NeZero k] (hk : T.card = k) :
    Nonempty (Canonical (v i) p (MMS n (v i) p) (thr v p i) k R D) := by sorry
