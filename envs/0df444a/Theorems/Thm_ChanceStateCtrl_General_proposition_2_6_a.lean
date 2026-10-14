-- Prove2me | Theorems.Thm_ChanceStateCtrl_General_proposition_2_6_a
-- name    : ChanceStateCtrl.General.proposition_2_6_a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:20:52.260848+00:00
-- url     : https://prove2.me/theorems/7e8a6896-3f4c-4bf6-b8b2-8e2a3eacb55e
-- title:
--   Proposition 2.6 (21), p. 8 — u* solves (9) iff DF(u*) ∈ λ∂^Cφ(u*), φ(u*) ≥ p, λ(φ(u*) − p) = 0 for some λ ≥ 0
-- statement:
--   Consider the probabilistically constrained problem (9),
--   $$
--   \min_{u\in U}F(u)\quad\text{s.t.}\quad\varphi(u)=\mathbb P(\omega\mid g(u,\xi(\omega))\le0)\ge p,\qquad p\in(0,1].
--   $$
--   Assume:
--
--   1. $U$ is a reflexive and separable Banach space;
--   2. $F:U\to\mathbb R$ is convex and Fréchet differentiable, with derivative $DF(u)\in U^*$;
--   3. $\xi$ is an $m$-dimensional centered Gaussian random vector $\mathcal N(0,\Sigma)$ with nondegenerate covariance matrix $\Sigma$;
--   4. $g:U\times\mathbb R^m\to\mathbb R$ is locally Lipschitzian and jointly convex in both variables;
--   5. there is a generalized Slater point $\hat u\in U$ with $\varphi(\hat u)>p$;
--   6. $u^*\in U$ is feasible, $\varphi(u^*)\ge p$, satisfies (10), $g(u^*,0)<0$, and either the moderate growth condition (12) holds at $u^*$ or the set $M=\{z\mid g(u^*,z)\le0\}$ is bounded.
--
--   Then $u^*$ is a solution (global minimizer) of (9) if and only if there is $\lambda\ge0$ with
--   $$
--   DF(u^*)\in\lambda\,\partial^C\varphi(u^*),\qquad\varphi(u^*)\ge p,\qquad\lambda(\varphi(u^*)-p)=0. \tag{21}
--   $$
--   Here $\partial^C$ is Clarke's subdifferential.
--
--   This is a necessary and sufficient multiplier rule for a nonconvex, nonsmooth chance-constrained program in a Banach space, with the Clarke subdifferential of the probability function in place of a gradient; it is the general result that the paper then specializes to a PDE-constrained control problem.
--
--   **Formalization Note** "$DF(u^*)\in\lambda\partial^C\varphi(u^*)$" is written as "there is $x^*\in\partial^C\varphi(u^*)$ with $DF(u^*)=\lambda x^*$", which is unambiguous at $\lambda=0$. Joint convexity of $g$ is stated in addition to the convexity of $g(u,\cdot)$ of Assumption 2.1, which it implies. A solution is a global minimizer over $\{u\mid\varphi(u)\ge p\}$. Conventions ($\Sigma^{1/2}$ in (12), the open ball in (12), the Clarke objects) are those of the Setting module.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 8, Proposition 2.6, first statement (21)

import Mathlib
import Definitions.Def_ChanceStateCtrl_General_Setting
open MeasureTheory ProbabilityTheory Filter Topology
open scoped MatrixOrder Pointwise

namespace ChanceStateCtrl.General

theorem proposition_2_6_a {Ω U : Type*} [MeasurableSpace Ω] [NormedAddCommGroup U] [NormedSpace ℝ U] {m : ℕ}
    (P : Measure Ω) (ξ : Ω → EuclideanSpace ℝ (Fin m)) (Sigma : Matrix (Fin m) (Fin m) ℝ)
    (g : U → EuclideanSpace ℝ (Fin m) → ℝ) (hA : Assumption21 P ξ Sigma g)
    (hg_jc : ConvexOn ℝ Set.univ (Function.uncurry g))
    (F : U → ℝ) (hF_convex : ConvexOn ℝ Set.univ F) (hF_diff : Differentiable ℝ F)
    (p : ℝ) (hp : p ∈ Set.Ioc (0 : ℝ) 1) (hslater : ∃ uh : U, p < probFn P ξ g uh)
    (us : U) (hfeas : p ≤ probFn P ξ g us) (h10 : g us 0 < 0)
    (h12 : ModerateGrowth g Sigma us ∨ Bornology.IsBounded {z | g us z ≤ 0}) :
    IsSolution {u | p ≤ probFn P ξ g u} F us ↔
      ∃ lam : ℝ, 0 ≤ lam ∧
        (∃ x ∈ clarkeSubdiff (probFn P ξ g) us, fderiv ℝ F us = lam • x) ∧
        p ≤ probFn P ξ g us ∧ lam * (probFn P ξ g us - p) = 0 := by sorry

end ChanceStateCtrl.General
