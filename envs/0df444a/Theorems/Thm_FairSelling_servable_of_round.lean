-- Prove2me | Theorems.Thm_FairSelling_servable_of_round
-- name    : FairSelling.servable_of_round
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-24T02:11:12.097811+00:00
-- url     : https://prove2.me/theorems/aad93e91-6f5c-418d-a43a-670dd5b485b3
-- title:
--   Fair Selling: servable of round
-- statement:
--   **One round of the main loop.**  If the active agent `i` holds a canonical partition of the
--   available resources into `|T|` parts, and if the state reached after the round is servable, then
--   the state before the round is servable.  The recursive hypothesis is given all the information
--   produced by the round (which agents were served, which part each of them received, and the fact
--   that the still-active agents find all of these parts unacceptable), since that is what is needed
--   to re-establish the invariant of the algorithm.
--
--   Source: https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsCanonical.lean#L388-L422
-- source:
--   https://github.com/yotam-gafni/FairAllocationWithOptionalSelling/blob/daed8afbbc6b4da634e8cbffa11e861f99533f56/RequestProject/TwoThirdsCanonical.lean#L388-L422

import Mathlib
import Definitions.Def_RequestProject_Selling
import Definitions.Def_RequestProject_SmallN
import Definitions.Def_RequestProject_TPSApprox
import Definitions.Def_RequestProject_TwoThirdsMatching
import Definitions.Def_RequestProject_TwoThirdsCanonical
set_option autoImplicit true
open scoped BigOperators
open FairSelling
open Finset
variable {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
omit [Fintype G]

theorem FairSelling.servable_of_round (v : Fin n → G → ℝ) (p : G → ℝ) (τ : Fin n → ℝ)
    {T : Finset (Fin n)} {R : Finset G} {D : ℝ} {μ : ℝ} {i : Fin n} (hi : i ∈ T)
    {k : ℕ} [NeZero k] (hk : T.card = k)
    (C : Canonical (v i) p μ (τ i) k R D)
    (hrec : ∀ (Kset : Finset (Fin n)) (part : Fin n → Fin k), i ∈ Kset → Kset ⊆ T →
        Set.InjOn part Kset →
        (∀ a ∈ T, a ∉ Kset → ∀ b ∈ Kset,
          vbarSum (v a) p (C.goods (part b)) + C.cash (part b) < τ a) →
        (∀ a ∈ Kset, a ≠ i → part a ≠ 0) → (Kset = T ∨ part i ≠ 0) →
        Servable v p τ (T \ Kset)
          (R \ ((Kset.image part).biUnion C.goods ∪ C.sold (Kset.image part)))
          (D + (∑ g ∈ C.sold (Kset.image part), p g)
              - ∑ j ∈ Kset.image part, C.cash j)) :
    Servable v p τ T R D := by sorry
