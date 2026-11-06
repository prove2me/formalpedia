-- Prove2me | Theorems.Thm_AuctionMatroidInt_lemma_5_5
-- name    : AuctionMatroidInt.lemma_5_5
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:31:05.424599+00:00
-- url     : https://prove2.me/theorems/577f1577-8bdc-4b0b-ac96-f752071e9378
-- title:
--   Lemma 5.5 — weight splitting: $(1-\varepsilon)\,w(\mathrm{OPT}_w)\le U(X,\pi)$
-- statement:
--   Under the standing assumptions ($M_1,M_2$ loopless matroids, $w>0$, $0<\varepsilon<1$), at any point of Algorithm 3,
--
--   $$
--   (1-\varepsilon)\,w(\mathrm{OPT}_w)\le U(X,\pi)=\pi(X)+\max_{B\in\mathcal B_1}q(B),
--   $$
--
--   where $\mathrm{OPT}_w$ is a maximum-weight common independent set and $q$ is induced by the current $(X,\pi)$.
--
--   The lemma makes $U$ an upper bound on the approximate optimum; Proposition 5.8 shows that $U$ comes down to the weight of the current solution.
--
--   **Formalization Note** "At any point" ranges over every configuration inside every round started at a round-start configuration; the bound is stated against every common independent set $Y$.
--
--   Differences from the source:
--
--   - encoding: a matroid M = (E, I) on a finite set E (nonempty hereditary family with the augmentation property) → CombOpt.MatroidPolytope.IsMatroid I for I : Finset α → Prop on a finite type α (ground set = α); reason: IsMatroid's axioms (∅ ∈ I, hereditary, all maximal independent subsets of a set have equal size) are equivalent to §2.1's; same instances
--   - generalization: the standing assumptions of §2.1 (pp.10–11): 1/ε is an integer, M₁, M₂ have no loops, w > 0, r_i(E) ≤ 2r (and 1/ε ≤ n+1 for unit weights) → only: M₁, M₂ loopless matroids, w > 0, 0 < ε < 1; reason: the proofs in §5 never use 1/ε ∈ ℤ or r_i(E) ≤ 2r; adding them back gives the source's statement as a special case
--   - encoding: “throughout the execution of Algorithm 3”, elements scanned “in an arbitrary order” → every configuration inside a round (Alg3Partial, any order of the scanned elements, any tie-break in Line 12) started at any round-start configuration (Alg3RoundStart, from X = ∅ with any number of rounds); reason: these are exactly the configurations reachable by Algorithm 3 run with some T; the initial π is arbitrary but read only on X = ∅
--   - encoding: π(e) = ⊥ for e ∉ X → π : α → ℝ, read only on X by every definition; reason: values of π off X never influence p̄, p, q, U, π(X) or a step; same executions
--   - encoding: w(OPT_w) for a maximum-weight common independent set OPT_w → the bound against w(Y) for every common independent Y; reason: equivalent, since OPT_w maximizes w over common independent sets (which exist: ∅)
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), Lemma 5.5, p.24 (PDF p.26)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_IsMatroid
import Definitions.Def_CombOpt_MatroidPolytope_weight
import Definitions.Def_AuctionMatroidInt_Loopless
import Definitions.Def_AuctionMatroidInt_potential
import Definitions.Def_AuctionMatroidInt_Alg3RoundStart

namespace AuctionMatroidInt

/-- **Lemma 5.5 (weight splitting).**
Huang, Kobayashi, Terao, *Auction-Based Algorithms for Weighted Matroid Intersection with
Near-Linear Query Complexity* (manuscript, sha256 2e12cb4a…), Lemma 5.5, p.24:
"At any point of Algorithm 3, we have (1 − ε) · w(OPT_w) ≤ U(X, π)."

**Standing assumptions** (§2.1, pp.10–11, "Throughout the paper, without loss of generality"):
`M₁ = (α, I₁)` and `M₂ = (α, I₂)` are matroids (`CombOpt.MatroidPolytope.IsMatroid`) without
loops, `w(e) > 0` for every `e`, and `0 < ε < 1`.

"At any point" is every configuration `s` inside every round (`Alg3Partial`) of every
round-start `(X*, π*)`; `U(X, π)` is `potential` of the current `(X, π)`. The bound
`(1 − ε) · w(OPT_w) ≤ U` is stated as `(1 − ε) · w(Y) ≤ U` for every common independent set
`Y`, which is the same since `OPT_w` is a maximum-weight common independent set. -/
theorem lemma_5_5 {α : Type*} [Fintype α] [DecidableEq α] (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (w : α → ℝ) (hw : ∀ e, 0 < w e) (I₁ I₂ : Finset α → Prop)
    (hI₁ : CombOpt.MatroidPolytope.IsMatroid I₁) (hI₂ : CombOpt.MatroidPolytope.IsMatroid I₂)
    (hL₁ : Loopless I₁) (hL₂ : Loopless I₂)
    (Xs : Finset α) (πs : α → ℝ) (hstart : Alg3RoundStart ε w I₁ I₂ Xs πs)
    (l : List α) (s : Alg3State α) (hs : Alg3Partial ε w I₁ I₂ Xs πs l s)
    (Y : Finset α) (hY₁ : I₁ Y) (hY₂ : I₂ Y) :
    (1 - ε) * CombOpt.MatroidPolytope.weight w Y ≤ potential ε w I₁ I₂ s.X s.π := by sorry

end AuctionMatroidInt
