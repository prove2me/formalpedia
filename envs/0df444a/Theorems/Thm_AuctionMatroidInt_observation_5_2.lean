-- Prove2me | Theorems.Thm_AuctionMatroidInt_observation_5_2
-- name    : AuctionMatroidInt.observation_5_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:30:43.975924+00:00
-- url     : https://prove2.me/theorems/739c2d5d-f80b-43e5-b89a-8c6e3eec1109
-- title:
--   Observation 5.2 — price bounds and the increase of $\pi(X)$
-- statement:
--   Assume the standing assumptions of the paper: $M_1,M_2$ are loopless matroids on $E$, $w(e)>0$ for all $e$, and $0<\varepsilon<1$. Throughout the execution of Algorithm 3:
--
--   1. $X\in\mathcal I_2$, and $\varepsilon w(e)\le\pi(e)<w(e)$ for each $e\in X$; in particular $\pi(X)\le w(X)$.
--   2. When Lines 7–14 are executed for $e\in E\setminus X^*$, the price $p(e)$ is unchanged and $\pi(X)$ increases by exactly $\varepsilon w(e)$:
--
--   $$
--   p_{\mathrm{after}}(e)=p_{\mathrm{before}}(e),\qquad \pi'(X')=\pi(X)+\varepsilon w(e).
--   $$
--
--   Part 2 is what converts the number of executed iterations into the increase $\Delta$ of $\pi(X)$ in Lemma 5.7; part 1 bounds $\pi(X)$ by the weight of a common independent set.
--
--   **Formalization Note** "Throughout the execution" ranges over every configuration inside every round started at a round-start configuration; in part 2, $e$ is the next scanned element and the condition of Line 6 holds.
--
--   Differences from the source:
--
--   - encoding: a matroid M = (E, I) on a finite set E (nonempty hereditary family with the augmentation property) → CombOpt.MatroidPolytope.IsMatroid I for I : Finset α → Prop on a finite type α (ground set = α); reason: IsMatroid's axioms (∅ ∈ I, hereditary, all maximal independent subsets of a set have equal size) are equivalent to §2.1's; same instances
--   - generalization: the standing assumptions of §2.1 (pp.10–11): 1/ε is an integer, M₁, M₂ have no loops, w > 0, r_i(E) ≤ 2r (and 1/ε ≤ n+1 for unit weights) → only: M₁, M₂ loopless matroids, w > 0, 0 < ε < 1; reason: the proofs in §5 never use 1/ε ∈ ℤ or r_i(E) ≤ 2r; adding them back gives the source's statement as a special case
--   - encoding: “throughout the execution of Algorithm 3”, elements scanned “in an arbitrary order” → every configuration inside a round (Alg3Partial, any order of the scanned elements, any tie-break in Line 12) started at any round-start configuration (Alg3RoundStart, from X = ∅ with any number of rounds); reason: these are exactly the configurations reachable by Algorithm 3 run with some T; the initial π is arbitrary but read only on X = ∅
--   - encoding: π(e) = ⊥ for e ∉ X → π : α → ℝ, read only on X by every definition; reason: values of π off X never influence p̄, p, q, U, π(X) or a step; same executions
-- source:
--   Huang, Kobayashi, Terao, Auction-Based Algorithms for Weighted Matroid Intersection with Near-Linear Query Complexity (manuscript, sha256 2e12cb4a…), Observation 5.2, p.22 (PDF p.24)

import Mathlib
import Definitions.Def_CombOpt_MatroidPolytope_IsMatroid
import Definitions.Def_CombOpt_MatroidPolytope_weight
import Definitions.Def_AuctionMatroidInt_Loopless
import Definitions.Def_AuctionMatroidInt_Alg3RoundStart

namespace AuctionMatroidInt

/-- **Observation 5.2.**
Huang, Kobayashi, Terao, *Auction-Based Algorithms for Weighted Matroid Intersection with
Near-Linear Query Complexity* (manuscript, sha256 2e12cb4a…), Observation 5.2, p.22:
"Throughout the execution of Algorithm 3, the following hold.
(a) X ∈ I₂, and εw(e) ≤ π(e) < w(e) for each e ∈ X. In particular, π(X) ≤ w(X).
(b) When Lines 7–14 are executed for e ∈ E \ X*, the value p(e) is unchanged and π(X)
increases by exactly εw(e)."

**Standing assumptions** (§2.1, pp.10–11, "Throughout the paper, without loss of generality"):
`M₁ = (α, I₁)` and `M₂ = (α, I₂)` are matroids (`CombOpt.MatroidPolytope.IsMatroid`) without
loops, `w(e) > 0` for every `e`, and `0 < ε < 1`.

"Throughout the execution" is every configuration `s` inside every round (`Alg3Partial`, which
includes the beginning of the round, `l = []`) of every round-start `(X*, π*)`
(`Alg3RoundStart`). In (b), `e` is the next scanned element (not in `X*`, not yet scanned),
the condition of Line 6 holds, and `s'` is the result of Lines 7–14.

**Formalization Note.** `π(X)` is `CombOpt.MatroidPolytope.weight π X`. -/
theorem observation_5_2 {α : Type*} [Fintype α] [DecidableEq α] (ε : ℝ) (hε : 0 < ε)
    (hε1 : ε < 1) (w : α → ℝ) (hw : ∀ e, 0 < w e) (I₁ I₂ : Finset α → Prop)
    (hI₁ : CombOpt.MatroidPolytope.IsMatroid I₁) (hI₂ : CombOpt.MatroidPolytope.IsMatroid I₂)
    (hL₁ : Loopless I₁) (hL₂ : Loopless I₂)
    (Xs : Finset α) (πs : α → ℝ) (hstart : Alg3RoundStart ε w I₁ I₂ Xs πs)
    (l : List α) (s : Alg3State α) (hs : Alg3Partial ε w I₁ I₂ Xs πs l s) :
    (I₂ s.X ∧ (∀ e ∈ s.X, ε * w e ≤ s.π e ∧ s.π e < w e) ∧
      CombOpt.MatroidPolytope.weight s.π s.X ≤ CombOpt.MatroidPolytope.weight w s.X) ∧
    (∀ (e : α) (s' : Alg3State α), e ∉ Xs → e ∉ l → Alg3Cond ε w I₁ I₂ Xs πs s e →
      Alg3Exec ε w I₂ e s s' →
      price ε w I₂ s'.X s'.π e = price ε w I₂ s.X s.π e ∧
        CombOpt.MatroidPolytope.weight s'.π s'.X =
          CombOpt.MatroidPolytope.weight s.π s.X + ε * w e) := by sorry

end AuctionMatroidInt
