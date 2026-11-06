-- Prove2me | Theorems.Thm_AuctionMatroidInt_lemma_5_4
-- name    : AuctionMatroidInt.lemma_5_4
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:30:40.96492+00:00
-- url     : https://prove2.me/theorems/9039e123-d2f9-48ad-a97a-be33bd60418d
-- title:
--   Lemma 5.4 — invariants of Algorithm 3
-- statement:
--   Under the standing assumptions ($M_1,M_2$ loopless matroids, $w>0$, $0<\varepsilon<1$):
--
--   1. at the beginning of each round, $X$ is contained in a $q$-maximum base of $M_1$, where $q$ is induced by $(X,\pi)$;
--   2. before and after each iteration of the inner for-loop in each round, $Y$ is contained in a $q^*$-maximum base of $M_1$, where $q^*$ is induced by $(X^*,\pi^*)$ at the beginning of the round;
--   3. $X\in\mathcal I_1\cap\mathcal I_2$ holds throughout the algorithm.
--
--   In the auction interpretation, Alice's aim of buying a $q^*$-maximum base of $M_1$ stays achievable throughout each round. Clause 3 shows that the output is a common independent set; clause 2 is a hypothesis of Lemma 5.1 in the proof of Lemma 5.7.
--
--   **Formalization Note** Clause 1 ranges over round-start configurations, clauses 2 and 3 over every configuration inside every round started at one.
--
--   Differences from the source:
--
--   - encoding: a matroid M = (E, I) on a finite set E (nonempty hereditary family with the augmentation property) → CombOpt.MatroidPolytope.IsMatroid I for I : Finset α → Prop on a finite type α (ground set = α); reason: IsMatroid's axioms (∅ ∈ I, hereditary, all maximal independent subsets of a set have equal size) are equivalent to §2.1's; same instances
--   - generalization: the standing assumptions of §2.1 (pp.10–11): 1/ε is an integer, M₁, M₂ have no loops, w > 0, r_i(E) ≤ 2r (and 1/ε ≤ n+1 for unit weights) → only: M₁, M₂ loopless matroids, w > 0, 0 < ε < 1; reason: the proofs in §5 never use 1/ε ∈ ℤ or r_i(E) ≤ 2r; adding them back gives the source's statement as a special case
--   - encoding: “throughout the execution of Algorithm 3”, elements scanned “in an arbitrary order” → every configuration inside a round (Alg3Partial, any order of the scanned elements, any tie-break in Line 12) started at any round-start configuration (Alg3RoundStart, from X = ∅ with any number of rounds); reason: these are exactly the configurations reachable by Algorithm 3 run with some T; the initial π is arbitrary but read only on X = ∅
--   - encoding: π(e) = ⊥ for e ∉ X → π : α → ℝ, read only on X by every definition; reason: values of π off X never influence p̄, p, q, U, π(X) or a step; same executions
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), Lemma 5.4, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_IsMatroid
import Definitions.Def_AuctionMatroidInt_Loopless
import Definitions.Def_AuctionMatroidInt_Alg3RoundStart

namespace AuctionMatroidInt

/-- **Lemma 5.4 (invariants of Algorithm 3).**
Huang, Kobayashi, Terao, *Auction-Based Algorithms for Weighted Matroid Intersection with
Near-Linear Query Complexity* (manuscript, sha256 2e12cb4a…), Lemma 5.4, p.23:
"At the beginning of each round, X is contained in a q-maximum base of M₁. Moreover, Y is
contained in a q*-maximum base of M₁ before and after each iteration of the inner for-loop in
each round, and X ∈ I₁ ∩ I₂ holds throughout the algorithm."

**Standing assumptions** (§2.1, pp.10–11, "Throughout the paper, without loss of generality"):
`M₁ = (α, I₁)` and `M₂ = (α, I₂)` are matroids (`CombOpt.MatroidPolytope.IsMatroid`) without
loops, `w(e) > 0` for every `e`, and `0 < ε < 1`.

The three clauses: (1) at every round-start `(X, π)`, `X` is contained in a `q`-maximum base of
`M₁`, `q` induced by `(X, π)`; (2) at every configuration `s` inside a round started at
`(X*, π*)` (before and after each iteration), `Y` is contained in a `q*`-maximum base of `M₁`,
`q*` induced by `(X*, π*)`; (3) at every such configuration `X ∈ I₁ ∩ I₂`. -/
theorem lemma_5_4 {α : Type*} [Fintype α] [DecidableEq α] (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (w : α → ℝ) (hw : ∀ e, 0 < w e) (I₁ I₂ : Finset α → Prop)
    (hI₁ : CombOpt.MatroidPolytope.IsMatroid I₁) (hI₂ : CombOpt.MatroidPolytope.IsMatroid I₂)
    (hL₁ : Loopless I₁) (hL₂ : Loopless I₂) :
    (∀ (X : Finset α) (π : α → ℝ), Alg3RoundStart ε w I₁ I₂ X π →
      ∃ B, IsMaxBase I₁ (utility ε w I₂ X π) B ∧ X ⊆ B) ∧
    (∀ (Xs : Finset α) (πs : α → ℝ) (l : List α) (s : Alg3State α),
      Alg3RoundStart ε w I₁ I₂ Xs πs → Alg3Partial ε w I₁ I₂ Xs πs l s →
      ∃ B, IsMaxBase I₁ (utility ε w I₂ Xs πs) B ∧ s.Y ⊆ B) ∧
    (∀ (Xs : Finset α) (πs : α → ℝ) (l : List α) (s : Alg3State α),
      Alg3RoundStart ε w I₁ I₂ Xs πs → Alg3Partial ε w I₁ I₂ Xs πs l s →
      I₁ s.X ∧ I₂ s.X) := by sorry

end AuctionMatroidInt
