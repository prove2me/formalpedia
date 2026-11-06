-- Prove2me | Theorems.Thm_AuctionMatroidInt_lemma_5_14
-- name    : AuctionMatroidInt.lemma_5_14
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:27:11.674244+00:00
-- url     : https://prove2.me/theorems/cec04f33-bed4-4356-8cbb-200266046173
-- title:
--   Lemma 5.14 — computing a price $p(e)$ with $O(\log r)$ queries
-- statement:
--   There is an absolute constant $C$ with the following property. Let $E$ be finite, $0<\varepsilon<1$, $w>0$, $X\subseteq E$, prices $\pi$ on $X$, and $e\in E$. There is a deterministic algorithm, given $\varepsilon,w,X,\pi,e$, that for every loopless matroid $M_2=(E,\mathcal I_2)$ with $X\in\mathcal I_2$ returns the price
--
--   $$
--   p(e)\ \text{induced by }X\text{ and }\pi\ \text{(display (2))}
--   $$
--
--   using at most $C\log(|X|+2)$ independence queries to $M_2$. In Algorithm 4, $X$ is common independent, so $|X|\le r$ and the bound is $O(\log r)$.
--
--   Together with Lemma 5.15 it bounds the number of queries of one round of Algorithm 4 by $O(n\log r)$.
--
--   **Formalization Note** The algorithm is a `QueryTree Unit α ℝ`; $C$ is chosen before the ground set.
--
--   Differences from the source:
--
--   - encoding: a matroid M = (E, I) on a finite set E (nonempty hereditary family with the augmentation property) → CombOpt.MatroidPolytope.IsMatroid I for I : Finset α → Prop on a finite type α (ground set = α); reason: IsMatroid's axioms (∅ ∈ I, hereditary, all maximal independent subsets of a set have equal size) are equivalent to §2.1's; same instances
--   - encoding: π(e) = ⊥ for e ∉ X → π : α → ℝ, read only on X by every definition; reason: values of π off X never influence p̄, p, q, U, π(X) or a step; same executions
--   - encoding: an algorithm computing p(e) using O(log r) independence queries → ∃ C (absolute, before α) and a QueryTree built from (ε, w, X, π, e) returning price ε w I₂ X π e; reason: the query model of §2.1
--   - generalization: O(log r) queries for the X, π maintained by Algorithm 4 (X ∈ I₁ ∩ I₂) → C · log(|X| + 2) for every X ∈ I₂ and every π; reason: |X| ≤ r for a common independent X, so the bound specializes to O(log r); the proof gives O(log |X|)
--   - reading: O(log r) → a bound with log(· + 2); reason: log r ≤ 0 for r ≤ 1; the two agree up to a constant factor for arguments ≥ 2
--   - generalization: the standing assumptions of §2.1 (1/ε integral, r_i(E) ≤ 2r, M₁ loopless) → not assumed (only 0 < ε < 1, w > 0, M₂ loopless with X ∈ I₂); reason: the computation involves only M₂; adding them gives the source's statement
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), Lemma 5.14, p.29 (PDF p.31)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_IsMatroid
import Definitions.Def_AuctionMatroidInt_Loopless
import Definitions.Def_AuctionMatroidInt_QueryTree
import Definitions.Def_AuctionMatroidInt_utility

namespace AuctionMatroidInt

/-- **Lemma 5.14 (computing a price with few queries).**
Huang, Kobayashi, Terao, *Auction-Based Algorithms for Weighted Matroid Intersection with
Near-Linear Query Complexity* (manuscript, sha256 2e12cb4a…), Lemma 5.14, p.29:
"Given X and π, for e ∈ E, we can compute p(e) using O(log r) independence queries."

There is an absolute constant `C` such that for every finite ground set `α`, every `0 < ε < 1`,
every `w > 0`, every `X`, `π` and `e` there is a deterministic query algorithm (a `QueryTree`
built from `ε, w, X, π, e`) which, for **every** loopless matroid `M₂ = (α, I₂)` with `X ∈ I₂`,
returns the price `p(e)` of display (2) induced by `X` and `π`, using at most
`C · log(|X| + 2)` independence queries to `M₂`.

**Formalization Note.** The matroid is reached only through `indepOracle` (one oracle, `Unit`).
The bound is in `|X|`, which is at most `r` for the common independent `X` of the algorithm, and
`log` is read as `log(· + 2)`. -/
theorem lemma_5_14 :
    ∃ C : ℝ, ∀ {α : Type} [Fintype α] [DecidableEq α] (ε : ℝ) (w : α → ℝ) (X : Finset α)
      (π : α → ℝ) (e : α), 0 < ε → ε < 1 → (∀ a, 0 < w a) →
      ∃ A : QueryTree Unit α ℝ, ∀ I₂ : Finset α → Prop,
        CombOpt.MatroidPolytope.IsMatroid I₂ → Loopless I₂ → I₂ X →
        A.run (indepOracle fun _ => I₂) = price ε w I₂ X π e ∧
          (A.queries (indepOracle fun _ => I₂) : ℝ) ≤ C * Real.log (X.card + 2) := by sorry

end AuctionMatroidInt
