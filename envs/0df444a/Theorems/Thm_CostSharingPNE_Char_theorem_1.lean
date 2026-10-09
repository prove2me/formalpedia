-- Prove2me | Theorems.Thm_CostSharingPNE_Char_theorem_1
-- name    : CostSharingPNE.Char.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:24:43.512259+00:00
-- url     : https://prove2.me/theorems/f66403f1-ae67-489d-abf3-4323c9cd8e5d
-- title:
--   Theorem 1, p. 9 — all games in 𝒢(N, f^𝕎, 𝕎) have a pure Nash equilibrium iff one weight system ω makes every f^W the GWSV rule of the distributed welfare (10)
-- statement:
--   Let $N=\{1,\dots,n\}$, $n>1$, be the players, $\mathbb W$ a nonempty set of local welfare functions, and $f^{\mathbb W}=\{f^W\}_{W\in\mathbb W}$ the corresponding distribution rules (not necessarily budget-balanced). For each $W\in\mathbb W$ let $W'=g_{SV}(W)$ be the welfare actually distributed by $f^W$,
--   $$
--   (\forall S\subseteq N)\qquad W'(S)=\sum_{i\in S} f^W(i,S). \tag{10}
--   $$
--   Then all games in $\mathcal G(N,f^{\mathbb W},\mathbb W)$ possess a pure Nash equilibrium if and only if there exists a weight system $\omega$ such that, for every $W\in\mathbb W$, the rule $f^W$ is equivalent to the generalized weighted Shapley value rule of $W'$:
--   $$
--   f^W(i,S)=f^{W'}_{GWSV}[\omega](i,S)\qquad\text{for all } S\subseteq N \text{ and } i\in S .
--   $$
--
--   The theorem characterizes completely the distribution rules that guarantee equilibrium existence for a fixed set of local welfare functions, with or without budget-balance: they are exactly the generalized weighted Shapley values on some ground welfare functions, and so equilibrium existence in all games forces a (generalized weighted) potential game.
--
--   **Formalization Note** The ground welfare is not quantified: it is the distributed welfare (10), written `distributed (f W)`. One weight system serves every $W\in\mathbb W$. "Equivalent" is equality at every $i\in S$, the only shares a game ever uses. The game class quantifies over every number $m>1$ of resources, every assignment of welfare functions from $\mathbb W$ to resources (repetitions allowed) and every family of nonempty action sets of arbitrary resource subsets.
-- source:
--   Gopalakrishnan, Marden, Wierman, arXiv:1402.3610v1, Theorem 1 and (10), p. 9

import Mathlib
import Definitions.Def_CostSharingPNE_Char_Setting
import Definitions.Def_CostSharingPNE_Char_WeightSystem

namespace CostSharingPNE.Char

theorem theorem_1 (n : ℕ) (hn : 1 < n) (𝕎 : Set (Welfare n)) (h𝕎 : 𝕎.Nonempty)
    (f : Welfare n → Rule n) :
    GuaranteesPNE 𝕎 f ↔
      ∃ ω : WeightSystem n, ∀ W ∈ 𝕎, ∀ S : Finset (Fin n), ∀ i ∈ S,
        f W i S = gwsv ω (distributed (f W)) i S := by sorry

end CostSharingPNE.Char
