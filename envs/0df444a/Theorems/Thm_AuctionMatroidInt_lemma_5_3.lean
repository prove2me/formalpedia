-- Prove2me | Theorems.Thm_AuctionMatroidInt_lemma_5_3
-- name    : AuctionMatroidInt.lemma_5_3
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:30:10.383194+00:00
-- url     : https://prove2.me/theorems/398630f7-2c8f-4c70-a2d1-9fe40cab4774
-- title:
--   Lemma 5.3 — prices never decrease, utilities never increase
-- statement:
--   Under the standing assumptions ($M_1,M_2$ loopless matroids, $w>0$, $0<\varepsilon<1$), for each $e'\in E$ the values $\bar p(e')$ and $p(e')$ induced by the current $(X,\pi)$ are monotonically non-decreasing, and $q(e')$ is monotonically non-increasing, throughout the execution of Algorithm 3: across every iteration of the inner for-loop,
--
--   $$
--   \bar p(e')\le\bar p_{\mathrm{after}}(e'),\qquad p(e')\le p_{\mathrm{after}}(e'),\qquad q_{\mathrm{after}}(e')\le q(e').
--   $$
--
--   In the auction interpretation, Bob never lowers a price. The lemma gives (H1) of Lemma 5.1 and is used in Lemmas 5.4 and 5.6.
--
--   **Formalization Note** Stated for every iteration (executed or not) at every configuration inside every round started at a round-start configuration; $X$ and $\pi$ do not change between rounds.
--
--   Differences from the source:
--
--   - encoding: a matroid M = (E, I) on a finite set E (nonempty hereditary family with the augmentation property) → CombOpt.MatroidPolytope.IsMatroid I for I : Finset α → Prop on a finite type α (ground set = α); reason: IsMatroid's axioms (∅ ∈ I, hereditary, all maximal independent subsets of a set have equal size) are equivalent to §2.1's; same instances
--   - generalization: the standing assumptions of §2.1 (pp.10–11): 1/ε is an integer, M₁, M₂ have no loops, w > 0, r_i(E) ≤ 2r (and 1/ε ≤ n+1 for unit weights) → only: M₁, M₂ loopless matroids, w > 0, 0 < ε < 1; reason: the proofs in §5 never use 1/ε ∈ ℤ or r_i(E) ≤ 2r; adding them back gives the source's statement as a special case
--   - encoding: “throughout the execution of Algorithm 3”, elements scanned “in an arbitrary order” → every configuration inside a round (Alg3Partial, any order of the scanned elements, any tie-break in Line 12) started at any round-start configuration (Alg3RoundStart, from X = ∅ with any number of rounds); reason: these are exactly the configurations reachable by Algorithm 3 run with some T; the initial π is arbitrary but read only on X = ∅
--   - encoding: π(e) = ⊥ for e ∉ X → π : α → ℝ, read only on X by every definition; reason: values of π off X never influence p̄, p, q, U, π(X) or a step; same executions
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), Lemma 5.3, p.23 (PDF p.25)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_IsMatroid
import Definitions.Def_AuctionMatroidInt_Loopless
import Definitions.Def_AuctionMatroidInt_Alg3RoundStart

namespace AuctionMatroidInt

/-- **Lemma 5.3 (prices never decrease, utilities never increase).**
Huang, Kobayashi, Terao, *Auction-Based Algorithms for Weighted Matroid Intersection with
Near-Linear Query Complexity* (manuscript, sha256 2e12cb4a…), Lemma 5.3, p.23:
"For each e′ ∈ E, p̄(e′) and p(e′) are monotonically non-decreasing and q(e′) is monotonically
non-increasing throughout the execution of Algorithm 3."

**Standing assumptions** (§2.1, pp.10–11, "Throughout the paper, without loss of generality"):
`M₁ = (α, I₁)` and `M₂ = (α, I₂)` are matroids (`CombOpt.MatroidPolytope.IsMatroid`) without
loops, `w(e) > 0` for every `e`, and `0 < ε < 1`.

Monotonicity is stated across every iteration of the inner for-loop of every round of every
execution: `s` is a configuration inside a round started at a round-start `(X*, π*)`, `e` is the
next scanned element, and `s'` is the configuration after the iteration (`Alg3Step`, executed or
not). The values `p̄, p, q` are those induced by the current `(X, π)`. Between rounds `X` and `π`
do not change, so this is monotonicity throughout the execution. -/
theorem lemma_5_3 {α : Type*} [Fintype α] [DecidableEq α] (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (w : α → ℝ) (hw : ∀ e, 0 < w e) (I₁ I₂ : Finset α → Prop)
    (hI₁ : CombOpt.MatroidPolytope.IsMatroid I₁) (hI₂ : CombOpt.MatroidPolytope.IsMatroid I₂)
    (hL₁ : Loopless I₁) (hL₂ : Loopless I₂)
    (Xs : Finset α) (πs : α → ℝ) (hstart : Alg3RoundStart ε w I₁ I₂ Xs πs)
    (l : List α) (s : Alg3State α) (hs : Alg3Partial ε w I₁ I₂ Xs πs l s)
    (e : α) (he : e ∉ Xs) (hel : e ∉ l) (s' : Alg3State α)
    (hstep : Alg3Step ε w I₁ I₂ Xs πs e s s') (e' : α) :
    pbar I₂ s.X s.π e' ≤ pbar I₂ s'.X s'.π e' ∧
      price ε w I₂ s.X s.π e' ≤ price ε w I₂ s'.X s'.π e' ∧
      utility ε w I₂ s'.X s'.π e' ≤ utility ε w I₂ s.X s.π e' := by sorry

end AuctionMatroidInt
