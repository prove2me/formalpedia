-- Prove2me | Theorems.Thm_AuctionMatroidInt_lemma_5_6
-- name    : AuctionMatroidInt.lemma_5_6
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:30:44.12019+00:00
-- url     : https://prove2.me/theorems/83f608bd-9f93-4d74-9e02-5e501fcfaeaf
-- title:
--   Lemma 5.6 — utilities left behind drop by a factor $1+\varepsilon$
-- statement:
--   Under the standing assumptions ($M_1,M_2$ loopless matroids, $w>0$, $0<\varepsilon<1$), consider a round of Algorithm 3, with $X^*,\pi^*$ and $q^*$ at its beginning, and let $Y'$ and $q'$ be the set $Y$ and the utility vector $q$ at the end of the round. If $e\in E\setminus Y'$ and $Y'+e$ is contained in a $q^*$-maximum base of $M_1$, then
--
--   $$
--   q'(e)\le\frac{q^*(e)}{1+\varepsilon}.
--   $$
--
--   This provides hypothesis (H2) of Lemma 5.1 in the proof of Lemma 5.7.
--
--   **Formalization Note** The round starts at a round-start configuration and may use any scan order and tie-break.
--
--   Differences from the source:
--
--   - encoding: a matroid M = (E, I) on a finite set E (nonempty hereditary family with the augmentation property) → CombOpt.MatroidPolytope.IsMatroid I for I : Finset α → Prop on a finite type α (ground set = α); reason: IsMatroid's axioms (∅ ∈ I, hereditary, all maximal independent subsets of a set have equal size) are equivalent to §2.1's; same instances
--   - generalization: the standing assumptions of §2.1 (pp.10–11): 1/ε is an integer, M₁, M₂ have no loops, w > 0, r_i(E) ≤ 2r (and 1/ε ≤ n+1 for unit weights) → only: M₁, M₂ loopless matroids, w > 0, 0 < ε < 1; reason: the proofs in §5 never use 1/ε ∈ ℤ or r_i(E) ≤ 2r; adding them back gives the source's statement as a special case
--   - encoding: “throughout the execution of Algorithm 3”, elements scanned “in an arbitrary order” → every configuration inside a round (Alg3Partial, any order of the scanned elements, any tie-break in Line 12) started at any round-start configuration (Alg3RoundStart, from X = ∅ with any number of rounds); reason: these are exactly the configurations reachable by Algorithm 3 run with some T; the initial π is arbitrary but read only on X = ∅
--   - encoding: π(e) = ⊥ for e ∉ X → π : α → ℝ, read only on X by every definition; reason: values of π off X never influence p̄, p, q, U, π(X) or a step; same executions
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), Lemma 5.6, p.25 (PDF p.27)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_IsMatroid
import Definitions.Def_AuctionMatroidInt_Loopless
import Definitions.Def_AuctionMatroidInt_Alg3RoundStart

namespace AuctionMatroidInt

/-- **Lemma 5.6.**
Huang, Kobayashi, Terao, *Auction-Based Algorithms for Weighted Matroid Intersection with
Near-Linear Query Complexity* (manuscript, sha256 2e12cb4a…), Lemma 5.6, p.25:
"Consider a round. Let Y′ and q′ be the set Y and the utility vector q at the end of the round.
If e ∈ E \ Y′ and Y′ + e is contained in a q*-maximum base of M₁, then q′(e) ≤ q*(e)/(1 + ε)."

**Standing assumptions** (§2.1, pp.10–11, "Throughout the paper, without loss of generality"):
`M₁ = (α, I₁)` and `M₂ = (α, I₂)` are matroids (`CombOpt.MatroidPolytope.IsMatroid`) without
loops, `w(e) > 0` for every `e`, and `0 < ε < 1`.

A round starts at a round-start `(X*, π*)` (`Alg3RoundStart`) and ends in `s'` (`Alg3Round`, any
scan order and tie-break); `Y′ = s'.Y`, `q′` is induced by `(s'.X, s'.π)`, and `q*` by
`(X*, π*)`. -/
theorem lemma_5_6 {α : Type*} [Fintype α] [DecidableEq α] (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (w : α → ℝ) (hw : ∀ e, 0 < w e) (I₁ I₂ : Finset α → Prop)
    (hI₁ : CombOpt.MatroidPolytope.IsMatroid I₁) (hI₂ : CombOpt.MatroidPolytope.IsMatroid I₂)
    (hL₁ : Loopless I₁) (hL₂ : Loopless I₂)
    (Xs : Finset α) (πs : α → ℝ) (hstart : Alg3RoundStart ε w I₁ I₂ Xs πs)
    (s' : Alg3State α) (hround : Alg3Round ε w I₁ I₂ Xs πs s')
    (e : α) (he : e ∉ s'.Y)
    (hbase : ∃ B, IsMaxBase I₁ (utility ε w I₂ Xs πs) B ∧ insert e s'.Y ⊆ B) :
    utility ε w I₂ s'.X s'.π e ≤ utility ε w I₂ Xs πs e / (1 + ε) := by sorry

end AuctionMatroidInt
