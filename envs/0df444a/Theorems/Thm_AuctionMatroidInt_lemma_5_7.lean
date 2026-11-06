-- Prove2me | Theorems.Thm_AuctionMatroidInt_lemma_5_7
-- name    : AuctionMatroidInt.lemma_5_7
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:31:00.182774+00:00
-- url     : https://prove2.me/theorems/cb88317c-c447-424f-83d2-b14fb48f1e28
-- title:
--   Lemma 5.7 — progress of $U$ in one round
-- statement:
--   Under the standing assumptions ($M_1,M_2$ loopless matroids, $w>0$, $0<\varepsilon<1$), consider a round of Algorithm 3. Let $X^*,\pi^*,U^*$ be $X,\pi,U$ at the beginning of the round and $X',\pi',U'$ at its end, and let $\Delta=\pi'(X')-\pi^*(X^*)$. Then
--
--   $$
--   U'\le\frac{U^*}{1+\varepsilon}+\varepsilon\,w(X^*)+2\Delta .
--   $$
--
--   If $\pi(X)$ increases little in a round, then $U$ decreases substantially; Proposition 5.8 combines this with Lemma 5.5 over the rounds.
--
--   **Formalization Note** The round starts at a round-start configuration and may use any scan order and tie-break; $U$ is `potential`.
--
--   Differences from the source:
--
--   - encoding: a matroid M = (E, I) on a finite set E (nonempty hereditary family with the augmentation property) → CombOpt.MatroidPolytope.IsMatroid I for I : Finset α → Prop on a finite type α (ground set = α); reason: IsMatroid's axioms (∅ ∈ I, hereditary, all maximal independent subsets of a set have equal size) are equivalent to §2.1's; same instances
--   - generalization: the standing assumptions of §2.1 (pp.10–11): 1/ε is an integer, M₁, M₂ have no loops, w > 0, r_i(E) ≤ 2r (and 1/ε ≤ n+1 for unit weights) → only: M₁, M₂ loopless matroids, w > 0, 0 < ε < 1; reason: the proofs in §5 never use 1/ε ∈ ℤ or r_i(E) ≤ 2r; adding them back gives the source's statement as a special case
--   - encoding: “throughout the execution of Algorithm 3”, elements scanned “in an arbitrary order” → every configuration inside a round (Alg3Partial, any order of the scanned elements, any tie-break in Line 12) started at any round-start configuration (Alg3RoundStart, from X = ∅ with any number of rounds); reason: these are exactly the configurations reachable by Algorithm 3 run with some T; the initial π is arbitrary but read only on X = ∅
--   - encoding: π(e) = ⊥ for e ∉ X → π : α → ℝ, read only on X by every definition; reason: values of π off X never influence p̄, p, q, U, π(X) or a step; same executions
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), Lemma 5.7, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_IsMatroid
import Definitions.Def_CombOpt_MatroidPolytope_weight
import Definitions.Def_AuctionMatroidInt_Loopless
import Definitions.Def_AuctionMatroidInt_potential
import Definitions.Def_AuctionMatroidInt_Alg3RoundStart

namespace AuctionMatroidInt

/-- **Lemma 5.7 (progress in one round).**
Huang, Kobayashi, Terao, *Auction-Based Algorithms for Weighted Matroid Intersection with
Near-Linear Query Complexity* (manuscript, sha256 2e12cb4a…), Lemma 5.7, p.25:
"Consider a round. Let X*, π*, and U* denote the objects X, π, and U at the beginning of the
round, respectively, and let X′, π′, and U′ denote the corresponding objects at the end of the
round. Let Δ := π′(X′) − π*(X*) be the increase of π(X) in the round. Then
U′ ≤ U*/(1 + ε) + ε w(X*) + 2Δ."

**Standing assumptions** (§2.1, pp.10–11, "Throughout the paper, without loss of generality"):
`M₁ = (α, I₁)` and `M₂ = (α, I₂)` are matroids (`CombOpt.MatroidPolytope.IsMatroid`) without
loops, `w(e) > 0` for every `e`, and `0 < ε < 1`.

A round starts at a round-start `(X*, π*)` and ends in `s'` (`Alg3Round`, any scan order and
tie-break), with `X′ = s'.X`, `π′ = s'.π`; `U = potential`. -/
theorem lemma_5_7 {α : Type*} [Fintype α] [DecidableEq α] (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (w : α → ℝ) (hw : ∀ e, 0 < w e) (I₁ I₂ : Finset α → Prop)
    (hI₁ : CombOpt.MatroidPolytope.IsMatroid I₁) (hI₂ : CombOpt.MatroidPolytope.IsMatroid I₂)
    (hL₁ : Loopless I₁) (hL₂ : Loopless I₂)
    (Xs : Finset α) (πs : α → ℝ) (hstart : Alg3RoundStart ε w I₁ I₂ Xs πs)
    (s' : Alg3State α) (hround : Alg3Round ε w I₁ I₂ Xs πs s') :
    potential ε w I₁ I₂ s'.X s'.π ≤
      potential ε w I₁ I₂ Xs πs / (1 + ε) + ε * CombOpt.MatroidPolytope.weight w Xs +
        2 * (CombOpt.MatroidPolytope.weight s'.π s'.X -
          CombOpt.MatroidPolytope.weight πs Xs) := by sorry

end AuctionMatroidInt
