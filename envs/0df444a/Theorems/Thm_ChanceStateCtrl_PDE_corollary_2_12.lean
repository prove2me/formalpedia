-- Prove2me | Theorems.Thm_ChanceStateCtrl_PDE_corollary_2_12
-- name    : ChanceStateCtrl.PDE.corollary_2_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:31.442171+00:00
-- url     : https://prove2.me/theorems/5b204794-d9d6-4976-8122-c036d264f320
-- title:
--   Corollary 2.12, p. 10 — with (26) and a generalized Slater point, Proposition 2.6's optimality conditions (21), (22) hold for (24)
-- statement:
--   Throughout, $D\subseteq\mathbb R^d$ ($d\in\{1,2,3\}$) is a nonempty, open, bounded domain of class S, $A^{-1}:L^2(D)\to C(\bar D)$ is the solution operator of the Dirichlet problem $-\Delta y=F$ in $D$, $y=0$ on $\partial D$ (in $H^1_0(D)\cap C(\bar D)$), $f_0,\varphi_1,\dots,\varphi_m\in L^2(D)$, and $S(u,z)=A^{-1}(u+f_0+\sum_i z_i\varphi_i)$, $P(u,z)=A^{-1}u+\sum_i z_iA^{-1}\varphi_i$ are the operators of (5). The constraint function of (24) is $g(u,z)=\max_{x\in\bar D}[S(u,z)](x)-\alpha$ for a threshold $\alpha\in\mathbb R$.
--
--   The random vector $\xi:\Omega\to\mathbb R^m$ ($m\ge1$) on a probability space $(\Omega,\mathcal F,\mathbb P)$ is measurable with law $\mathcal N(0,\Sigma)$, $\Sigma$ positive definite, and $\varphi(u)=\mathbb P(\omega\mid g(u,\xi(\omega))\le0)$ is the probability function of (24).
--
--   Let $F:L^2(D)\to\mathbb R$ be convex and Fréchet differentiable, $p\in(0,1]$, and suppose there is $\hat u$ with $\varphi(\hat u)>p$. Let $u^*$ be feasible, $\varphi(u^*)\ge p$, with expected state satisfying (26) at $u^*$. Then for problem (24), $\min\{F(u)\mid\varphi(u)\ge p\}$:
--
--   1. $u^*$ is a solution if and only if there is $\lambda\ge0$ with
--   $$DF(u^*)\in\lambda\,\partial^C\varphi(u^*),\quad\varphi(u^*)\ge p,\quad\lambda(\varphi(u^*)-p)=0;\tag{21}$$
--   2. if $u^*$ is a solution, there is $\lambda\ge0$ with
--   $$DF(u^*)\in\lambda\int_{\mathbb S^{m-1}}\partial^C_ue(u^*,v)\,d\mu_\zeta(v),\quad\varphi(u^*)\ge p,\quad\lambda(\varphi(u^*)-p)=0;\tag{22}$$
--   3. if (16) holds at $u^*$ or the set $M=\{z\mid g(u^*,z)\le0\}$ of (11) is bounded, then (22) is also sufficient for $u^*$ to be a solution.
--
--   This is Proposition 2.6 (p. 8) instantiated for the PDE problem, the bridge from the general theory to the explicit conditions of Theorem 2.16.
--
--   **Formalization Note** The domain hypotheses are binders: `IsOpen D`, `Bornology.IsBounded D`, `D.Nonempty`, `d = 1 ∨ d = 2 ∨ d = 3`, `IsClassS D`, and `[CompactSpace (closure D)]` (a consequence of boundedness, needed for the norm on $C(\bar D)$). Nonemptiness of $D$ is added: the page's $\max_{x\in\bar D}$ needs it, and for $D=\emptyset$ Lean's supremum over the empty type is $0$. $A^{-1}$ is a continuous linear map `Ainv` together with the hypothesis `hA` that `Ainv F` is, on $\bar D$, a weak solution `IsDirichletSol D F y` for every $F\in L^2(D)$; Lemma 1.2 shows such a map exists and its uniqueness clause makes it the paper's $A^{-1}$. The Clarke directional derivative is the page-3 limsup with denominator $t$ (the page prints $h$, a misprint), and the dual of $L^2(D)$ is identified with $L^2(D)$ through the inner product, as on p. 11. $\Sigma^{1/2}$ is the positive semidefinite square root `CFC.sqrt Sigma`, the root used by Mathlib's `multivariateGaussian`. A solution is a global minimizer over $\{u\mid\varphi(u)\ge p\}$; $DF(u^*)$ is the Riesz gradient `gradient F us`. Condition (16) is stated as "$\partial^C_ue(u^*,v)$ is a subsingleton for $\mu_\zeta$-a.e. $v$".
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 10, Corollary 2.12 (with Proposition 2.6, p. 8)

import Mathlib
import Definitions.Def_ChanceStateCtrl_PDE_Setting
import Definitions.Def_ChanceStateCtrl_PDE_Model

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal Pointwise

namespace ChanceStateCtrl.PDE

/-- Corollary 2.12 (p. 10): under (26) at a feasible `u*` and a generalized Slater point `û` with
`φ(û) > p`, Proposition 2.6 holds for (24): (21) is necessary and sufficient for optimality, (22)
is necessary, and (22) is sufficient when (16) holds or the set `M` of (11) is bounded. -/
theorem corollary_2_12 {d m : ℕ} (D : Set (EuclideanSpace ℝ (Fin d)))
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
    (us : L2 D) (hus : p ≤ probFn P ξ (gPDE Ainv f₀ φ α) us)
    (h26 : ∀ x : closure D, stateS Ainv f₀ φ us 0 x < α)
    (hslater : ∃ uh : L2 D, p < probFn P ξ (gPDE Ainv f₀ φ α) uh) :
    (IsSolution {u | p ≤ probFn P ξ (gPDE Ainv f₀ φ α) u} F us ↔
      ∃ lam : ℝ, 0 ≤ lam ∧ gradient F us ∈ lam • clarkeSubdiffL2 (probFn P ξ (gPDE Ainv f₀ φ α)) us ∧
        p ≤ probFn P ξ (gPDE Ainv f₀ φ α) us ∧ lam * (probFn P ξ (gPDE Ainv f₀ φ α) us - p) = 0) ∧
    (IsSolution {u | p ≤ probFn P ξ (gPDE Ainv f₀ φ α) u} F us →
      ∃ lam : ℝ, 0 ≤ lam ∧
        gradient F us ∈ lam • aumannL2 (sphereLaw m) (fun v => clarkeSubdiffL2 (fun u => radialProb (gPDE Ainv f₀ φ α) Sigma u v) us) ∧
        p ≤ probFn P ξ (gPDE Ainv f₀ φ α) us ∧ lam * (probFn P ξ (gPDE Ainv f₀ φ α) us - p) = 0) ∧
    (((∀ᵐ v ∂(sphereLaw m), (clarkeSubdiffL2 (fun u => radialProb (gPDE Ainv f₀ φ α) Sigma u v) us).Subsingleton) ∨
        Bornology.IsBounded {z : EuclideanSpace ℝ (Fin m) | gPDE Ainv f₀ φ α us z ≤ 0}) →
      (∃ lam : ℝ, 0 ≤ lam ∧
        gradient F us ∈ lam • aumannL2 (sphereLaw m) (fun v => clarkeSubdiffL2 (fun u => radialProb (gPDE Ainv f₀ φ α) Sigma u v) us) ∧
        p ≤ probFn P ξ (gPDE Ainv f₀ φ α) us ∧ lam * (probFn P ξ (gPDE Ainv f₀ φ α) us - p) = 0) →
      IsSolution {u | p ≤ probFn P ξ (gPDE Ainv f₀ φ α) u} F us) := by sorry

end ChanceStateCtrl.PDE
