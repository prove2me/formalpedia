-- Prove2me | Theorems.Thm_BregmanRelax_EqConstr_lagrange_2_7
-- name    : BregmanRelax.EqConstr.lagrange_2_7
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T01:16:16.456963+00:00
-- url     : https://prove2.me/theorems/6c48dd72-cee2-4e72-8746-666cf39b66d3
-- title:
--   (2.7)–(2.8) — the $D$-projection onto a hyperplane satisfies a Lagrange condition
-- statement:
--   Let $S\subset E^p$, let $f : E^p\to\mathbb R$ have gradient $g(x)$ (relative to $S$) at every $x\in S$, let $A_i$ be the hyperplane $\{x \mid (A_i,x)=b_i\}$ of the $i$-th equation of $Ax=b$, and let $D(x,y)=f(x)-f(y)-(g(y),x-y)$ as in (1.4). Assume that $D$, the hyperplanes and a $D$-projection map $P$ satisfy conditions I–IV and VI of §1 (so in particular $P_ix\in A_i\cap S$ minimizes $D(\cdot,x)$ over $A_i\cap S$ for every $x\in S$), and that $P$ maps interior points of $S$ to interior points of $S$:
--   $$x\in\operatorname{int}S\ \Longrightarrow\ P_ix\in\operatorname{int}S\quad\text{for every } i .$$
--   Then for every $i$ and every $x\in\operatorname{int}S$ there is a real number $\lambda$ with
--   $$g(P_ix)=g(x)+\lambda A_i,\qquad (A_i,P_ix)=b_i. \qquad (2.7)\text{–}(2.8)$$
--
--   These are the Lagrange conditions for minimizing $D(\cdot,x)$ on the hyperplane $A_i$. In the proof of Theorem 3 they are applied to $x=x^n$, $P_ix=x^{n+1}$, the step of the relaxation sequence.
--
--   **Formalization Note** The translation prints (2.7) as "$g(x^{n-1})=g(x^n)+\lambda A_i$"; the intended reading, confirmed by (2.14) on p. 211, is $g(x^{n+1})$. The hypothesis $x\in\operatorname{int}S$, together with the interior hypothesis on $P$ from Theorem 3, is what the paper's proof uses at each step. The multiplier $\lambda$ is named `lam` in Lean ($\lambda$ is a Lean keyword).
-- source:
--   Bregman, The relaxation method of finding the common point of convex sets and its application to the solution of problems in convex programming, USSR Comput. Math. Math. Phys. 7(3) (1967), p. 210, proof of Theorem 3, (2.7)–(2.8)

import Mathlib
import Definitions.Def_BregmanRelax_Cyclic_DConditions
import Definitions.Def_BregmanRelax_EqConstr_Program

namespace BregmanRelax.EqConstr

/-- (2.7)–(2.8), proof of Theorem 3 (Bregman 1967, p. 210): if `P` is the D-projection map of
condition II for the hyperplanes `A_i` and `D` of (1.4), and `P` maps interior points of `S` to
interior points of `S`, then for every interior point `x` of `S` the D-projection `P i x` onto `A_i`
satisfies `g(P i x) = g(x) + λ A_i` for some real `λ` (named `lam`) and `(A_i, P i x) = b_i`. -/
theorem lagrange_2_7 {p m : ℕ} {S : Set (EuclideanSpace ℝ (Fin p))}
    {f : EuclideanSpace ℝ (Fin p) → ℝ}
    {g : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    {a : Fin m → EuclideanSpace ℝ (Fin p)} {b : Fin m → ℝ}
    {P : Fin m → EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)}
    (hfg : ∀ x ∈ S, HasGradientWithinAt f (g x) S x)
    (hA : BregmanRelax.Cyclic.DConditions (hyperplane a b) S (bregmanD f g) P)
    (hint : ∀ i, ∀ x ∈ interior S, P i x ∈ interior S) :
    ∀ i, ∀ x ∈ interior S, ∃ lam : ℝ,
      g (P i x) = g x + lam • a i ∧ inner ℝ (a i) (P i x) = b i := by sorry

end BregmanRelax.EqConstr
