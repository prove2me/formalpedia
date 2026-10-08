-- Prove2me | Theorems.Thm_BregmanRelax_IneqConstr_step1_Z0
-- name    : BregmanRelax.IneqConstr.step1_Z0
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T10:15:31.294069+00:00
-- url     : https://prove2.me/theorems/c9e88395-7538-4052-8991-41af38f02ad5
-- title:
--   Theorem 4, proof, step 1 — every iterate lies in $Z_0$: $u^n\ge 0$ and $g(x^n)=u^nA$
-- statement:
--   **Setting.** Let $E^p$ be the $p$-dimensional Euclidean space and $S\subset E^p$ a convex set. Let $f$ be a strictly convex function on $S$, continuously differentiable over $S$ with gradient $g(x)$, and continuous over the closure $\bar S$. Let $A$ be an $m\times p$ matrix, $m\ge 1$, with nonzero rows $A_1,\dots,A_m$, and $b\in E^m$. Consider the problem
--   $$\text{minimize } f(x)\quad\text{subject to}\quad Ax\ge b,\quad x\in\bar S \qquad (2.11)\text{–}(2.13),$$
--   with feasible set $R=\{x\in E^p \mid Ax\ge b,\ x\in\bar S\}$, assumed nonempty. Let $D(x,y)=f(x)-f(y)-(g(y),x-y)$ be the function (1.4), and let $A_i=\{x \mid (A_i,x)=b_i\}$ also denote the $i$-th hyperplane. Assume the conditions of Theorem 3: $D$ satisfies conditions I–VI of §1 for the family of hyperplanes $A_i$ with $D$-projections $P_i$, $D$ satisfies condition (2) of Note 1, and the $D$-projection of every interior point of $S$ onto every $A_i$ is an interior point of $S$. Condition V is assumed for the points $z\in R$.
--
--   Let $(x^n,u^n)_{n\ge 0}$ be any sequence of pairs produced by the method of pp. 211–212 (cyclic control $i_n$, initial point $x^0\in Z_0\cap\operatorname{int}S$ with $u^0\ge 0$ and $g(x^0)=u^0A$, and steps 3(a)–(c); see the definition item *Program*), where $Z_0=\{x\in S \mid g(x)=uA \text{ for some } u\ge 0\}$ and $\varphi(x,u)=f(x)-(u,Ax-b)$.
--
--   Then for every $n$ the multiplier vector stays nonnegative and certifies $x^n\in Z_0$:
--   $$u^n\ge 0\qquad\text{and}\qquad g(x^n)=u^nA=\sum_{j=1}^m u^n_jA_j .$$
--
--   This invariant makes the method a dual-feasible scheme: $u^n$ is a nonnegative Lagrange multiplier vector for the current point, and it is what the potential estimates of the later steps rely on.
--
--   **Formalization Note** The rows of $A$ are vectors $a_i$ of `EuclideanSpace ℝ (Fin p)`, $uA$ is $\sum_i u_i a_i$, and the gradient $g$ is explicit data tied to $f$ by `HasGradientWithinAt` on $S$ (the paper does not assume $S$ open). The $D$-projections are a fixed map $P$. Condition V is assumed for $z\in R$, the inequality-feasible set, because that is where the proof applies it; the paper's §1 form ($z$ in the intersection of the hyperplanes) could be vacuous for an inequality system. The conditions I–VI are encoded as in the definition item *DConditions* (one-sided form of IV, sequential compactness). The translation reads "If for the index $i_k$ or (3c) is satisfied"; the case "(3b)" is dropped by the translation.
-- source:
--   Bregman, The relaxation method of finding the common point of convex sets and its application to the solution of problems in convex programming, USSR Comput. Math. Math. Phys. 7(3) (1967), pp. 212, Theorem 4, proof, step 1, (2.20)–(2.21)

import Mathlib
import Definitions.Def_BregmanRelax_Cyclic_DConditions
import Definitions.Def_BregmanRelax_IneqConstr_Program

namespace BregmanRelax.IneqConstr

/-- Theorem 4, proof, step 1 (Bregman 1967, p. 212): every iterate of the method lies in
`Z_0`, i.e. `u^n ≥ 0` and `g(x^n) = u^n A`.
Standing hypotheses of §2 (pp. 208–211): `f` strictly convex and continuously
differentiable over the convex set `S ⊆ E^p` (gradient map `g`), continuous over `S̄`; all rows
`a i` of `A` nonzero; the feasible set `R = {Ax ≥ b} ∩ S̄` nonempty; the conditions of Theorem 3:
`D` of (1.4) satisfies conditions I–VI (with the D-projection map `P` onto the hyperplanes `A_i`)
and condition (2), and `P` maps interior points of `S` to interior points of `S`; condition V for
the points `z ∈ R`. `(x, u)` is any run of the method (cyclic control, `x 0 ∈ Z_0 ∩ int S`). -/
theorem step1_Z0 {p m : ℕ} {S : Set (EuclideanSpace ℝ (Fin p))}
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
    ∀ n, (∀ j, 0 ≤ u n j) ∧ g (x n) = ∑ j, u n j • a j := by sorry

end BregmanRelax.IneqConstr
