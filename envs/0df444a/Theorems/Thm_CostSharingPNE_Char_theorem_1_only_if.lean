-- Prove2me | Theorems.Thm_CostSharingPNE_Char_theorem_1_only_if
-- name    : CostSharingPNE.Char.theorem_1_only_if
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-04T16:31:39.772847+00:00
-- url     : https://prove2.me/theorems/31806850-882b-41f8-9e13-7c874b533220
-- title:
--   Theorem 1 (only if), p. 9 / Appendix A — equilibria in all games of 𝒢(N, f^𝕎, 𝕎) force one ω with f^W = GWSV[ω] of the distributed welfare (10)
-- statement:
--   This is the "only if" (necessity) direction of Theorem 1 of Gopalakrishnan–Marden–Wierman, the part to which Appendix A is devoted ("we only need to prove one direction").
--
--   Let $N=\{1,\dots,n\}$, $n>1$, be the players, $\mathbb W$ a nonempty set of local welfare functions, and $f^{\mathbb W}=\{f^W\}_{W\in\mathbb W}$ the corresponding distribution rules (not necessarily budget-balanced). For each $W\in\mathbb W$ let $W'=g_{SV}(W)$ be the welfare actually distributed by $f^W$,
--   $$
--   W'(S)=\sum_{i\in S} f^W(i,S)\qquad(S\subseteq N). \tag{10}
--   $$
--   If every game in $\mathcal G(N,f^{\mathbb W},\mathbb W)$ possesses a pure Nash equilibrium, then there is a single weight system $\omega=(\lambda,\Sigma)$ such that, for every $W\in\mathbb W$,
--   $$
--   f^W(i,S)=f^{W'}_{GWSV}[\omega](i,S)\qquad\text{for all } S\subseteq N \text{ and } i\in S .
--   $$
--
--   Together with the converse (generalized weighted Shapley values guarantee equilibria, Hart–Mas-Colell), this gives the full characterization of Theorem 1: equilibrium existence in all games forces every rule to be a generalized weighted Shapley value of the welfare it distributes, with one common weight system.
--
--   **Formalization Note** Same conventions as `CostSharingPNE.Char.theorem_1`: the game class quantifies over every number $m>1$ of resources, every assignment of welfare functions from $\mathbb W$ to resources (repetitions allowed) and every family of nonempty action sets. The rules are indexed by the elements of $\mathbb W$, and two different $W_1,W_2\in\mathbb W$ may distribute the same welfare $W'$; the statement still asks for one $\omega$ serving all of them.
-- source:
--   Gopalakrishnan, Marden, Wierman, arXiv:1402.3610v1, Theorem 1 and (10), p. 9; Appendix A opening paragraph and Proposition 7, pp. 16-18

import Mathlib
import Definitions.Def_CostSharingPNE_Char_Setting
import Definitions.Def_CostSharingPNE_Char_WeightSystem

namespace CostSharingPNE.Char

theorem theorem_1_only_if (n : ℕ) (hn : 1 < n) (𝕎 : Set (Welfare n)) (h𝕎 : 𝕎.Nonempty)
    (f : Welfare n → Rule n) (hpne : GuaranteesPNE 𝕎 f) :
    ∃ ω : WeightSystem n, ∀ W ∈ 𝕎, ∀ S : Finset (Fin n), ∀ i ∈ S,
      f W i S = gwsv ω (distributed (f W)) i S := by sorry

end CostSharingPNE.Char
