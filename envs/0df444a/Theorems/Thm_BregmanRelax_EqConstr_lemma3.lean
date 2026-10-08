-- Prove2me | Theorems.Thm_BregmanRelax_EqConstr_lemma3
-- name    : BregmanRelax.EqConstr.lemma3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:16:02.081002+00:00
-- url     : https://prove2.me/theorems/35e1c395-aed2-421c-b188-10d32a9b9a9d
-- title:
--   Lemma 3 — a feasible point in the closure of $Z$ solves the equality-constrained program
-- statement:
--   Let $S\subset E^p$ be convex, and let $f : E^p\to\mathbb R$ be strictly convex on $S$, differentiable on $S$ (relative to $S$) with gradient $g(x)$ at each $x\in S$, with $g$ continuous on $S$, and $f$ continuous on the closure $\bar S$. Let $A$ be an $m\times p$ matrix with rows $A_1,\dots,A_m$, let $b\in E^m$, and consider the problem
--   $$\text{minimize } f(x)\quad\text{subject to}\quad Ax=b,\ x\in\bar S, \qquad (2.1)\text{–}(2.3)$$
--   with feasible set $R=\{x\in E^p \mid Ax=b,\ x\in\bar S\}$. Let $D(x,y)=f(x)-f(y)-(g(y),x-y)$ as in (1.4), and assume condition (2): if $y^n\in S$ and $y^n\to y^*\in\bar S$, then $D(y^*,y^n)\to 0$. Let $Z$ be the set of points $x\in S$ with $g(x)=uA$ for some $u\in E^m$, and $\bar Z$ its closure.
--
--   **Lemma 3.** If $y^*\in R\cap\bar Z$, then $y^*$ is a solution of (2.1)–(2.3):
--   $$f(y^*)\le f(x)\qquad\text{for every } x\in R .$$
--
--   Points of $Z$ are exactly the points of $S$ at which the Lagrange multiplier condition of the problem holds; the lemma says that a feasible limit of such points is optimal. It is the final step in the proof of Theorem 3.
--
--   **Formalization Note** The paper prints condition (2) with "$y^*\in S$"; it is applied here at $y^*\in R\subset\bar S$, so it is assumed for limits in $\bar S$. "Continuously differentiable over $S$" is a gradient map $g$ with $f$ differentiable relative to $S$ at every point of $S$ and $g$ continuous on $S$; $S$ is not assumed open. Of the standing hypotheses of §2, only these and condition (2) are assumed; dropping the others (nonzero rows, conditions I–VI) makes the statement stronger.
-- source:
--   Bregman, The relaxation method of finding the common point of convex sets and its application to the solution of problems in convex programming, USSR Comput. Math. Math. Phys. 7(3) (1967), p. 209, Lemma 3 (standing assumptions of §2, pp. 208–209)

import Mathlib
import Definitions.Def_BregmanRelax_EqConstr_Program

namespace BregmanRelax.EqConstr

/-- Lemma 3 (Bregman 1967, p. 209): a feasible point `y*` of problem (2.1)–(2.3) that lies in the
closure of `Z` minimizes `f` over the feasible set `R = {x | Ax = b} ∩ S̄`. -/
theorem lemma3 {p m : ℕ} {S : Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    {a : Fin m → EuclideanSpace ℝ (Fin p)} {b : Fin m → ℝ}
    (hS : Convex ℝ S) (hfc : StrictConvexOn ℝ S f)
    (hfg : ∀ x ∈ S, HasGradientWithinAt f (g x) S x) (hgc : ContinuousOn g S)
    (hfcl : ContinuousOn f (closure S))
    (h2 : Cond2 S (bregmanD f g))
    (y' : EuclideanSpace ℝ (Fin p)) (hyR : y' ∈ feasibleEq a b S)
    (hyZ : y' ∈ closure (Zset S g a)) :
    ∀ x ∈ feasibleEq a b S, f y' ≤ f x := by sorry

end BregmanRelax.EqConstr
