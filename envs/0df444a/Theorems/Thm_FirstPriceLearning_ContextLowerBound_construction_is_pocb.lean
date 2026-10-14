-- Prove2me | Theorems.Thm_FirstPriceLearning_ContextLowerBound_construction_is_pocb
-- name    : FirstPriceLearning.ContextLowerBound.construction_is_pocb
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T08:34:13.134318+00:00
-- url     : https://prove2.me/theorems/11879163-e2ef-463e-a01e-e451f8ce7848
-- title:
--   The hard instance is a partially ordered contextual bandit with $\beta = 1$ and independence number $\alpha$
-- statement:
--   Let $\alpha\ge1$, $M\ge1$ and $T$ satisfy $K=(\alpha+1)M\le T$, and let $u\in\{0,1,\dots,\alpha\}^M$. Consider the action set $\mathcal A=[M]\times\{0,\dots,\alpha\}$, the feedback graph $G$ with edges $(i_1,j_1)\to(i_2,j_2)$ for $i_1<i_2$ and $(i,j)\to(i,0)$ for $j\ne0$, and the Bernoulli product law $P^u$ of the proof of Theorem 6. Then:
--
--   1. $(G,P^u)$ together with the usual order $\le$ on the contexts $[M]$ is a partially ordered contextual bandit (Definition 3);
--   2. $G$ has independence number exactly $\alpha$;
--   3. $([M],\le)$ has independence number $\beta=1$.
--
--   This checks that the instances used in the lower bound belong to the class over which Theorem 6 takes its supremum.
--
--   **Formalization Note.** Definition 3's second condition is checked with the selection $a^\star_u(c)=(c,u_c)$ of optimal actions; the hypothesis $K\le T$ makes all Bernoulli parameters lie in $[0,1]$.
-- source:
--   Han, Zhou, Weissman, Optimal No-regret Learning in Repeated First-price Auctions, arXiv:2003.09795v7, p. 22, proof of Theorem 6 (construction of G and the check of Definition 3 with β = 1)

import Mathlib
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Model
import Definitions.Def_FirstPriceLearning_ContextLowerBound_Construction

open MeasureTheory

namespace FirstPriceLearning.ContextLowerBound

theorem construction_is_pocb (M α T : ℕ) (hα : 1 ≤ α) (hM : 1 ≤ M)
    (hT : (α + 1) * M ≤ T) (u : Fin M → Fin (α + 1)) :
    IsPartiallyOrderedContextualBandit (feedbackGraph M α) (hardLaw M α T u)
        (fun c₁ c₂ : Fin M => c₁ ≤ c₂) ∧
      HasIndependenceNumber (feedbackGraph M α) α ∧
      HasOrderIndependenceNumber (fun c₁ c₂ : Fin M => c₁ ≤ c₂) 1 := by sorry

end FirstPriceLearning.ContextLowerBound
