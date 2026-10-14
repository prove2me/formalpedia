-- Prove2me | Theorems.Thm_ChanceStateCtrl_PDE_theorem_2_16
-- name    : ChanceStateCtrl.PDE.theorem_2_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:37.141898+00:00
-- url     : https://prove2.me/theorems/caacce12-b219-4c94-95fb-1cc9ace7b8ea
-- title:
--   Theorem 2.16, pp. 14–15 — explicit necessary (and, under Theorem 2.15's equality conditions, sufficient) optimality conditions (43), (44) for (23)
-- statement:
--   Throughout, $D\subseteq\mathbb R^d$ ($d\in\{1,2,3\}$) is a nonempty, open, bounded domain of class S, $A^{-1}:L^2(D)\to C(\bar D)$ is the solution operator of the Dirichlet problem $-\Delta y=F$ in $D$, $y=0$ on $\partial D$ (in $H^1_0(D)\cap C(\bar D)$), $f_0,\varphi_1,\dots,\varphi_m\in L^2(D)$, and $S(u,z)=A^{-1}(u+f_0+\sum_i z_i\varphi_i)$, $P(u,z)=A^{-1}u+\sum_i z_iA^{-1}\varphi_i$ are the operators of (5). The constraint function of (24) is $g(u,z)=\max_{x\in\bar D}[S(u,z)](x)-\alpha$ for a threshold $\alpha\in\mathbb R$.
--
--   The random vector $\xi:\Omega\to\mathbb R^m$ ($m\ge1$) on a probability space $(\Omega,\mathcal F,\mathbb P)$ is measurable with law $\mathcal N(0,\Sigma)$, $\Sigma$ positive definite, and $\varphi(u)=\mathbb P(\omega\mid g(u,\xi(\omega))\le0)$ is the probability function of (24).
--
--   Let $F:L^2(D)\to\mathbb R$ be convex and Fréchet differentiable and $p\in(0,1]$. Consider problem (23), equivalently (24): minimize $F(u)$ over $u\in L^2(D)$ subject to $\varphi(u)\ge p$. Assume there is a control $\hat u$ with $\varphi(\hat u)>p$ (41), and let $u^*$ be feasible, $\varphi(u^*)\ge p$, with expected state $\tilde y=S(u^*,0)$ satisfying $\tilde y(x)<\alpha$ for all $x\in\bar D$ (42). Write $y^*(\cdot,\omega)=S(u^*,\xi(\omega))$.
--
--   1. If $u^*$ is a solution, there is $\lambda\ge0$ with
--   $$DF(u^*)\in-\lambda\int_{\{v\in\mathbb S^{m-1}\mid\rho(u^*,v)<\infty\}}\chi(\rho(u^*,v))\cdot\operatorname{clco}\Big\{\frac{1}{[P(0,\Sigma^{1/2}v)](x)}\,u_x\ \Big|\ x\in M^*(u^*,v)\Big\}\,d\mu_\zeta(v)\tag{43}$$
--   and
--   $$\lambda\big(\mathbb P(y^*(x,\omega)\le\alpha\ \ \forall x\in D)-p\big)=0.\tag{44}$$
--   2. If $M^*(u^*,v)$ is a singleton for $\mu_\zeta$-a.e. $v$ with $\rho(u^*,v)<\infty$, or the set $\{z\mid g(u^*,z)\le0\}$ is bounded, then any $\lambda\ge0$ with (43) and (44) certifies that $u^*$ is a solution.
--
--   This is the paper's main result: optimality conditions for an elliptic control problem with a probabilistic uniform state constraint, written entirely in terms of the problem data (Green-type functions $u_x$, the expected state, and the radius function).
--
--   **Formalization Note** The domain hypotheses are binders: `IsOpen D`, `Bornology.IsBounded D`, `D.Nonempty`, `d = 1 ∨ d = 2 ∨ d = 3`, `IsClassS D`, and `[CompactSpace (closure D)]` (a consequence of boundedness, needed for the norm on $C(\bar D)$). Nonemptiness of $D$ is added: the page's $\max_{x\in\bar D}$ needs it, and for $D=\emptyset$ Lean's supremum over the empty type is $0$. $A^{-1}$ is a continuous linear map `Ainv` together with the hypothesis `hA` that `Ainv F` is, on $\bar D$, a weak solution `IsDirichletSol D F y` for every $F\in L^2(D)$; Lemma 1.2 shows such a map exists and its uniqueness clause makes it the paper's $A^{-1}$. The Clarke directional derivative is the page-3 limsup with denominator $t$ (the page prints $h$, a misprint), and the dual of $L^2(D)$ is identified with $L^2(D)$ through the inner product, as on p. 11. $\Sigma^{1/2}$ is the positive semidefinite square root `CFC.sqrt Sigma`, the root used by Mathlib's `multivariateGaussian`. The page says "a solution to (9)"; problem (9) is the abstract problem of §2.1 and the theorem is about its instance (23) = (24), so the feasible set is $\{u\mid\varphi(u)\ge p\}$ and a solution is a global minimizer there. $DF(u^*)$ is the Riesz gradient. (44) is stated with the event over the open set $D$, as printed. The random state $y^*(\cdot,\omega)$ solving (23b)–(23c) is $S(u^*,\xi(\omega))$.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, pp. 14–15, Theorem 2.16

import Mathlib
import Definitions.Def_ChanceStateCtrl_PDE_Setting
import Definitions.Def_ChanceStateCtrl_PDE_Model

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal Pointwise

namespace ChanceStateCtrl.PDE

/-- Theorem 2.16 (pp. 14–15): explicit optimality conditions for the probabilistically
state-constrained problem (23) = (24). With a strict Slater control `û` (41) and a feasible `u*`
whose expected state satisfies (42), optimality of `u*` implies the existence of `λ ≥ 0` with (43)
and (44); and (43)–(44) are sufficient under Theorem 2.15's conditions for equality in (40). -/
theorem theorem_2_16 {d m : ℕ} (D : Set (EuclideanSpace ℝ (Fin d)))
    (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D) (hDne : D.Nonempty)
    (hd : d = 1 ∨ d = 2 ∨ d = 3) (hDS : IsClassS D)
    [CompactSpace (closure D)] (Ainv : L2 D →L[ℝ] C(closure D, ℝ))
    (hA : ∀ F : L2 D, ∃ y, IsDirichletSol D (⇑F) y ∧ ∀ x : closure D, Ainv F x = y x)
    (f₀ : L2 D) (φ : Fin m → L2 D) (α : ℝ)
    (hm : 0 < m) (Sigma : Matrix (Fin m) (Fin m) ℝ) (hSigma : Sigma.PosDef)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (hξlaw : P.map ξ = multivariateGaussian 0 Sigma)
    (F : L2 D → ℝ) (hFconv : ConvexOn ℝ Set.univ F) (hFdiff : Differentiable ℝ F)
    (p : ℝ) (hp : p ∈ Set.Ioc (0 : ℝ) 1)
    (h41 : ∃ uh : L2 D, p < probFn P ξ (gPDE Ainv f₀ φ α) uh)
    (us : L2 D) (hus : p ≤ probFn P ξ (gPDE Ainv f₀ φ α) us)
    (h42 : ∀ x : closure D, stateS Ainv f₀ φ us 0 x < α) :
    (IsSolution {u | p ≤ probFn P ξ (gPDE Ainv f₀ φ α) u} F us →
      ∃ lam : ℝ, 0 ≤ lam ∧ (∃ y ∈ integralSet Ainv f₀ φ α Sigma us, gradient F us = -lam • y) ∧
        lam * ((P {w | ∀ x : closure D, x.1 ∈ D → stateS Ainv f₀ φ us (ξ w) x ≤ α}).toReal - p) = 0) ∧
    (EqCond Ainv f₀ φ α Sigma us →
      ∀ lam : ℝ, 0 ≤ lam → (∃ y ∈ integralSet Ainv f₀ φ α Sigma us, gradient F us = -lam • y) →
        lam * ((P {w | ∀ x : closure D, x.1 ∈ D → stateS Ainv f₀ φ us (ξ w) x ≤ α}).toReal - p) = 0 →
        IsSolution {u | p ≤ probFn P ξ (gPDE Ainv f₀ φ α) u} F us) := by sorry

end ChanceStateCtrl.PDE
