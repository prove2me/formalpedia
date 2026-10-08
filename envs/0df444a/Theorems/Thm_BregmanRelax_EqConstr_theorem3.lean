-- Prove2me | Theorems.Thm_BregmanRelax_EqConstr_theorem3
-- name    : BregmanRelax.EqConstr.theorem3
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:16:40.95957+00:00
-- url     : https://prove2.me/theorems/8c8efaec-9717-499d-91c2-76dee29305d2
-- title:
--   Theorem 3 — a convergent relaxation started in $Z\cap\operatorname{int}S$ solves the equality-constrained program
-- statement:
--   **Setting (§2, pp. 208–209).** Let $S\subset E^p$ be convex, and let $f : E^p\to\mathbb R$ be strictly convex and continuously differentiable over $S$ (gradient $g(x)$ at $x\in S$) and continuous over $\bar S$. Let $A$ be an $m\times p$ matrix with nonzero rows $A_1,\dots,A_m$ and $b\in E^m$, and consider
--   $$\text{minimize } f(x)\quad\text{subject to}\quad Ax=b,\ x\in\bar S \qquad (2.1)\text{–}(2.3),$$
--   with feasible set $R=\{x \mid Ax=b,\ x\in\bar S\}$, assumed nonempty. Let $A_i=\{x\mid (A_i,x)=b_i\}$ also denote the $i$-th hyperplane, let $D(x,y)=f(x)-f(y)-(g(y),x-y)$ as in (1.4), and assume that $D$ with the $D$-projections $P_i$ onto the hyperplanes satisfies conditions I–VI of §1 and condition (2). Let $Z$ be the set of $x\in S$ with $g(x)=uA$ for some $u\in E^m$.
--
--   **Theorem 3.** Suppose that the $D$-projection of every point of $\operatorname{int}S$ onto every $A_i$ lies in $\operatorname{int}S$. Let $(i_n)$ be any relaxation control and $x^0, x^1,\dots$ the relaxation sequence, $x^{n+1}=P_{i_n}x^n$, with initial point
--   $$x^0\in Z\cap\operatorname{int}S .$$
--   If $x^n\to x^*\in R$, then $x^*$ is a solution of (2.1)–(2.3):
--   $$f(x^*)\le f(y)\qquad\text{for every } y\in R .$$
--
--   The theorem turns the feasibility method of §1 into an optimization method: by starting at a point where the Lagrange condition holds, any control under which the relaxation converges into $R$ (for instance the controls of Theorems 1–2) produces the minimizer of $f$ over $R$. Convergence is a hypothesis of the theorem, not a conclusion.
--
--   **Formalization Note** (a) The control $i : \mathbb N\to\{0,\dots,m-1\}$ is arbitrary, and convergence $x^n\to x^*\in R$ is assumed. (b) The paper's "Theorems 1 − 3" in the parenthetical example means Theorems 1–2. (c) Condition (2) is assumed for limits $y^*\in\bar S$ (the paper prints $y^*\in S$; its use at $x^*\in R$ needs $\bar S$). (d) Condition V is assumed for the points of $R\cap S$, as in §1. (e) "Continuously differentiable over $S$" is a gradient map $g$ relative to $S$, continuous on $S$; $S$ is not assumed open, and only the interior hypothesis on $P$ is made, as in the paper. (f) The conventions of the definitions (fixed projection map $P$, one-sided form of condition IV, sequential compactness) apply.
-- source:
--   Bregman, The relaxation method of finding the common point of convex sets and its application to the solution of problems in convex programming, USSR Comput. Math. Math. Phys. 7(3) (1967), pp. 209–210, Theorem 3 (standing assumptions of §2, pp. 208–209)

import Mathlib
import Definitions.Def_BregmanRelax_Cyclic_DConditions
import Definitions.Def_BregmanRelax_EqConstr_Program

namespace BregmanRelax.EqConstr

/-- Theorem 3 (Bregman 1967, pp. 209–210). Standing hypotheses of §2: `f` strictly convex and
continuously differentiable over the convex set `S ⊆ E^p` (gradient map `g`), continuous over `S̄`;
all rows `a i` of `A` nonzero; the feasible set `R = {Ax = b} ∩ S̄` nonempty; `D` of (1.4) satisfies
conditions I–VI (with the D-projection map `P` onto the hyperplanes `A_i`) and condition (2).
If `P` maps interior points of `S` to interior points of `S`, then for every relaxation control
`i` and every relaxation sequence `x` started at `x 0 ∈ Z ∩ int S` that converges to a point
`x* ∈ R`, the point `x*` minimizes `f` over `R`. -/
theorem theorem3 {p m : ℕ} {S : Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    {a : Fin m → EuclideanSpace ℝ (Fin p)} {b : Fin m → ℝ}
    {P : Fin m → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    (hS : Convex ℝ S) (hfc : StrictConvexOn ℝ S f)
    (hfg : ∀ x ∈ S, HasGradientWithinAt f (g x) S x) (hgc : ContinuousOn g S)
    (hfcl : ContinuousOn f (closure S))
    (ha : ∀ i, a i ≠ 0)
    (hRne : (feasibleEq a b S).Nonempty)
    (hA : BregmanRelax.Cyclic.DConditions (hyperplane a b) S (bregmanD f g) P)
    (hV : BregmanRelax.Cyclic.CondV S (bregmanD f g) (feasibleEq a b S ∩ S))
    (h2 : Cond2 S (bregmanD f g))
    (hint : ∀ i, ∀ x ∈ interior S, P i x ∈ interior S)
    (i : ℕ → Fin m) (x : ℕ → EuclideanSpace ℝ (Fin p)) (hx : BregmanRelax.Cyclic.IsRelaxSeq S P i x)
    (hx0 : x 0 ∈ Zset S g a ∩ interior S)
    (x' : EuclideanSpace ℝ (Fin p)) (hlim : Filter.Tendsto x Filter.atTop (nhds x'))
    (hx'R : x' ∈ feasibleEq a b S) :
    ∀ y ∈ feasibleEq a b S, f x' ≤ f y := by sorry

end BregmanRelax.EqConstr
