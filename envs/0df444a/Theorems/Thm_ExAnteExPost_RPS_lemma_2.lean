-- Prove2me | Theorems.Thm_ExAnteExPost_RPS_lemma_2
-- name    : ExAnteExPost.RPS.lemma_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:41.576726+00:00
-- url     : https://prove2.me/theorems/9a6a6a0d-e75f-4128-a9ef-8aa06a8c6a73
-- title:
--   Lemma 2, p. 11 — every integral allocation returned by Algorithm 1 satisfies EF1
-- statement:
--   Fix an instance with $n \ge 1$ agents, a favorite-good choice rule and an admissible decomposition rule. Every integral allocation $B$ that Algorithm 1 returns with positive probability is envy-free up to one good: for all agents $i, h$ with $B_h \ne \emptyset$ there is a good $j \in B_h$ with
--   $$v_i(B_i) \ge v_i(B_h \setminus \{j\}) .$$
--
--   This is the ex-post half of Theorem 2.
--
--   **Formalization Note.** "Returned" is read as "returned with positive probability"; a term of weight zero of a decomposition is never sampled, and the lemma can fail on it.
-- source:
--   Freeman, Shah, Vaish, Best of Both Worlds: Ex-Ante and Ex-Post Fairness in Resource Allocation, arXiv:2005.14122v1, p. 11, Lemma 2

import Mathlib
import Definitions.Def_ExAnteExPost_RPS_Model

namespace ExAnteExPost.RPS
open Finset

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G] [DecidableEq G]

/-- Lemma 2, p. 11: every integral allocation returned by Algorithm 1 (with positive
probability) is EF1. -/
theorem lemma_2 [Nonempty N] (I : Instance N G) (pick : PickRule N G)
    (hpick : IsFavoritePick I pick) (D : FracAlloc N G → Decomp N G) (hD : IsBvNOracle D) :
    ∀ e ∈ algorithm1 pick D, 0 < e.1 → IsEF1 I e.2 := by sorry
end ExAnteExPost.RPS
