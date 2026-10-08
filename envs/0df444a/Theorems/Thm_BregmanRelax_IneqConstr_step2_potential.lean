-- Prove2me | Theorems.Thm_BregmanRelax_IneqConstr_step2_potential
-- name    : BregmanRelax.IneqConstr.step2_potential
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T10:15:29.911451+00:00
-- url     : https://prove2.me/theorems/067b202c-2dd8-45f7-8b57-09c8226b6bfa
-- title:
--   Theorem 4, proof, step 2 — $\varphi(x^{n+1},u^{n+1})-\varphi(x^n,u^n)\ge D(x^{n+1},x^n)$ (2.22)–(2.24)
-- statement:
--   **Setting.** Let $E^p$ be the $p$-dimensional Euclidean space and $S\subset E^p$ a convex set. Let $f$ be a strictly convex function on $S$, continuously differentiable over $S$ with gradient $g(x)$, and continuous over the closure $\bar S$. Let $A$ be an $m\times p$ matrix, $m\ge 1$, with nonzero rows $A_1,\dots,A_m$, and $b\in E^m$. Consider the problem
--   $$\text{minimize } f(x)\quad\text{subject to}\quad Ax\ge b,\quad x\in\bar S \qquad (2.11)\text{–}(2.13),$$
--   with feasible set $R=\{x\in E^p \mid Ax\ge b,\ x\in\bar S\}$, assumed nonempty. Let $D(x,y)=f(x)-f(y)-(g(y),x-y)$ be the function (1.4), and let $A_i=\{x \mid (A_i,x)=b_i\}$ also denote the $i$-th hyperplane. Assume the conditions of Theorem 3: $D$ satisfies conditions I–VI of §1 for the family of hyperplanes $A_i$ with $D$-projections $P_i$, $D$ satisfies condition (2) of Note 1, and the $D$-projection of every interior point of $S$ onto every $A_i$ is an interior point of $S$. Condition V is assumed for the points $z\in R$.
--
--   Let $(x^n,u^n)_{n\ge 0}$ be any sequence of pairs produced by the method of pp. 211–212 (cyclic control $i_n$, initial point $x^0\in Z_0\cap\operatorname{int}S$ with $u^0\ge 0$ and $g(x^0)=u^0A$, and steps 3(a)–(c); see the definition item *Program*), where $Z_0=\{x\in S \mid g(x)=uA \text{ for some } u\ge 0\}$ and $\varphi(x,u)=f(x)-(u,Ax-b)$.
--
--   Then for every $n$,
--   $$\varphi(x^{n+1},u^{n+1})-\varphi(x^n,u^n)\ \ge\ D(x^{n+1},x^n).$$
--
--   In case (a) of the step this is the equality (2.23), in case (c) the inequality (2.24), and in case (b) it reads $0\ge D(x^n,x^n)=0$. Since $D\ge 0$ on $S\times S$, it implies the monotonicity (2.22), $\varphi(x^{n+1},u^{n+1})\ge\varphi(x^n,u^n)$: the potential $\varphi$ is a Lyapunov function of the method.
--
--   **Formalization Note** The rows of $A$ are vectors $a_i$ of `EuclideanSpace ℝ (Fin p)`, $uA$ is $\sum_i u_i a_i$, and the gradient $g$ is explicit data tied to $f$ by `HasGradientWithinAt` on $S$ (the paper does not assume $S$ open). The $D$-projections are a fixed map $P$. Condition V is assumed for $z\in R$, the inequality-feasible set, because that is where the proof applies it; the paper's §1 form ($z$ in the intersection of the hyperplanes) could be vacuous for an inequality system. The conditions I–VI are encoded as in the definition item *DConditions* (one-sided form of IV, sequential compactness).
-- source:
--   Bregman, The relaxation method of finding the common point of convex sets and its application to the solution of problems in convex programming, USSR Comput. Math. Math. Phys. 7(3) (1967), pp. 212–213, Theorem 4, proof, step 2, (2.22)–(2.24)

import Mathlib
import Definitions.Def_BregmanRelax_Cyclic_DConditions
import Definitions.Def_BregmanRelax_IneqConstr_Program

namespace BregmanRelax.IneqConstr

/-- Theorem 4, proof, step 2, (2.22)–(2.24) (Bregman 1967, pp. 212–213): the potential
`φ(x, u) = f(x) - (u, Ax - b)` increases along the method by at least `D(x^{n+1}, x^n)`.
Standing hypotheses of §2 (pp. 208–211): `f` strictly convex and continuously
differentiable over the convex set `S ⊆ E^p` (gradient map `g`), continuous over `S̄`; all rows
`a i` of `A` nonzero; the feasible set `R = {Ax ≥ b} ∩ S̄` nonempty; the conditions of Theorem 3:
`D` of (1.4) satisfies conditions I–VI (with the D-projection map `P` onto the hyperplanes `A_i`)
and condition (2), and `P` maps interior points of `S` to interior points of `S`; condition V for
the points `z ∈ R`. `(x, u)` is any run of the method (cyclic control, `x 0 ∈ Z_0 ∩ int S`). -/
theorem step2_potential {p m : ℕ} {S : Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    {a : Fin m → EuclideanSpace ℝ (Fin p)} {b : Fin m → ℝ}
    {P : Fin m → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    (hS : Convex ℝ S) (hfc : StrictConvexOn ℝ S f)
    (hfg : ∀ x ∈ S, HasGradientWithinAt f (g x) S x) (hgc : ContinuousOn g S)
    (hfcl : ContinuousOn f (closure S))
    (ha : ∀ i, a i ≠ 0)
    (hRne : (feasibleIneq a b S).Nonempty)
    (hA : BregmanRelax.Cyclic.DConditions (BregmanRelax.EqConstr.hyperplane a b) S (BregmanRelax.EqConstr.bregmanD f g) P)
    (h2 : BregmanRelax.EqConstr.Cond2 S (BregmanRelax.EqConstr.bregmanD f g))
    (hint : ∀ i, ∀ x ∈ interior S, P i x ∈ interior S)
    (hV : BregmanRelax.Cyclic.CondV S (BregmanRelax.EqConstr.bregmanD f g) (feasibleIneq a b S))
    (hm : 0 < m) (x : ℕ → EuclideanSpace ℝ (Fin p)) (u : ℕ → Fin m → ℝ)
    (hx : IsMethodRun hm S g a b x u) :
    ∀ n, BregmanRelax.EqConstr.bregmanD f g (x (n + 1)) (x n) ≤ phi f a b (x (n + 1)) (u (n + 1)) - phi f a b (x n) (u n) := by sorry

end BregmanRelax.IneqConstr
