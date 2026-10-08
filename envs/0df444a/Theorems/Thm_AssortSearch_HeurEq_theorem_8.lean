-- Prove2me | Theorems.Thm_AssortSearch_HeurEq_theorem_8
-- name    : AssortSearch.HeurEq.theorem_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:32:29.385201+00:00
-- url     : https://prove2.me/theorems/9b3d5c76-0721-4996-8869-b6e8958de9ed
-- title:
--   Theorem 8: the heuristic equilibrium of no-search assortment planning is never deeper than optimal, $x^*\le x^o$
-- statement:
--   A retailer carries the $x$ most popular of $n$ product variants with preferences $v_1\ge\dots\ge v_n>0$ (no-purchase preference $v_0>0$), margins with $m_j\ge m_k$ whenever $v_j\ge v_k$ and an operational cost $c$ that is concave and increasing on $[0,1]$ with $c(0)\ge0$. Consumers behave according to the independent assortment search model with constant $\lambda>0$, but the retailer plans with the traditional no-search MNL model, re-estimating preferences from the sales of each assortment it carries.
--
--   Let $x^*$ be a heuristic equilibrium of this process: $1\le x^*\le n$ and $x^*$ maximises the predicted profit $\pi(\cdot\mid\hat v(x^*))$ over the depths $0,\dots,n$. Let $x^o$ be an optimal assortment, $\pi(x^o)=\max_{0\le x\le n}\pi(x)$, such that every deeper assortment is strictly worse: $\pi(x)<\pi(x^o)$ for $x^o<x\le n$. Then
--   $$x^*\le x^o.$$
--
--   The heuristic equilibrium never contains more variants than the optimal assortment: a retailer that ignores consumer search risks choosing an assortment that is too narrow, never one that is too deep.
--
--   **Formalization Note** Independent assortment model only; the paper dismisses the overlapping case with "the similar process", which would also need the search threshold $\bar U(x)$ to be monotone. The paper speaks of "the optimal assortment", presuming uniqueness; the strict-deeper condition on $x^o$ is implied by uniqueness, and without it the conclusion can fail for a shallower optimum. $c(0)\ge0$ is added (the positivity step needs it). $x^*\ge 1$ is part of the equilibrium: at $x^*=0$ nothing is observed. Optimality of $x^o$ is over depths, as in the paper's proof.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 23 (PDF 25), Theorem 8 (independent assortment model; proof pp. 23–24)

import Mathlib
import Definitions.Def_AssortSearch_HeurEq_Model

namespace AssortSearch.HeurEq

open RetailVariety.Structure

/-- Theorem 8 (p. 23), independent assortment model: the heuristic equilibrium resulting from
the iterative application of the no-search assortment planning model never contains more variants
than the optimal assortment, `x* ≤ x^o`. Here `x^o` maximises the true profit over the depths
`0, …, n` and every deeper depth is strictly worse (implied by the uniqueness of "the optimal
assortment" that the paper presumes). The heuristic equilibrium has `x* ≥ 1`; at `x* = 0`
nothing is observed and the claim would be trivial. -/
theorem theorem_8 {n : ℕ} (lam : ℝ) (m : Fin n → ℝ) (c : ℝ → ℝ)
    (v : Fin n → ℝ) (v0 : ℝ)
    (hv : ∀ i, 0 < v i) (hanti : Antitone v) (hv0 : 0 < v0) (hlam : 0 < lam)
    (hm : ∀ j k : Fin n, v k ≤ v j → m k ≤ m j)
    (hcc : ConcaveOn ℝ (Set.Icc 0 1) c) (hcm : MonotoneOn c (Set.Icc 0 1))
    (hc0 : 0 ≤ c 0)
    (xstar xo : ℕ) (heq : IsHeuristicEquilibrium lam m c v v0 xstar)
    (hopt : IsOptimalDepth lam m c v v0 xo)
    (hdeeper : ∀ x : ℕ, xo < x → x ≤ n → trueProfit lam m c v v0 x < trueProfit lam m c v v0 xo) :
    xstar ≤ xo := by sorry

end AssortSearch.HeurEq
