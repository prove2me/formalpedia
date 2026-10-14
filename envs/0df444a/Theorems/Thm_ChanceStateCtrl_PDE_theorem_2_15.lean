-- Prove2me | Theorems.Thm_ChanceStateCtrl_PDE_theorem_2_15
-- name    : ChanceStateCtrl.PDE.theorem_2_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:42.260478+00:00
-- url     : https://prove2.me/theorems/c1f13936-c4e1-4181-827b-804cac18bbb9
-- title:
--   Theorem 2.15, p. 14 — under (26), φ is locally Lipschitz and ∂ᶜφ(ū) ⊆ −∫_{ρ<∞} χ(ρ)·clco{…} dμ_ζ (40), with equality under singleton M* or bounded M
-- statement:
--   Throughout, $D\subseteq\mathbb R^d$ ($d\in\{1,2,3\}$) is a nonempty, open, bounded domain of class S, $A^{-1}:L^2(D)\to C(\bar D)$ is the solution operator of the Dirichlet problem $-\Delta y=F$ in $D$, $y=0$ on $\partial D$ (in $H^1_0(D)\cap C(\bar D)$), $f_0,\varphi_1,\dots,\varphi_m\in L^2(D)$, and $S(u,z)=A^{-1}(u+f_0+\sum_i z_i\varphi_i)$, $P(u,z)=A^{-1}u+\sum_i z_iA^{-1}\varphi_i$ are the operators of (5). The constraint function of (24) is $g(u,z)=\max_{x\in\bar D}[S(u,z)](x)-\alpha$ for a threshold $\alpha\in\mathbb R$.
--
--   The random vector $\xi:\Omega\to\mathbb R^m$ ($m\ge1$) on a probability space $(\Omega,\mathcal F,\mathbb P)$ is measurable with law $\mathcal N(0,\Sigma)$, $\Sigma$ positive definite, and $\varphi(u)=\mathbb P(\omega\mid g(u,\xi(\omega))\le0)$ is the probability function of (24).
--
--   Fix $\bar u\in L^2(D)$ with (26). Then $\varphi$ is locally Lipschitzian around $\bar u$ and
--   $$\partial^C\varphi(\bar u)\subseteq-\int_{\{v\in\mathbb S^{m-1}\mid\rho(\bar u,v)<\infty\}}\chi(\rho(\bar u,v))\cdot\operatorname{clco}\Big\{\frac{1}{[P(0,\Sigma^{1/2}v)](x)}\,u_x\ \Big|\ x\in M^*(\bar u,v)\Big\}\,d\mu_\zeta(v),\tag{40}$$
--   with $M^*$, $u_x$ as in Lemma 2.14. The inclusion is an equality if $M^*(\bar u,v)$ is a singleton for $\mu_\zeta$-a.e. $v$ with $\rho(\bar u,v)<\infty$, or if the set $M=\{z\mid g(\bar u,z)\le0\}$ of (11) is bounded.
--
--   This is a fully explicit upper estimate of the subdifferential of the probability function in terms of the PDE data.
--
--   **Formalization Note** The domain hypotheses are binders: `IsOpen D`, `Bornology.IsBounded D`, `D.Nonempty`, `d = 1 ∨ d = 2 ∨ d = 3`, `IsClassS D`, and `[CompactSpace (closure D)]` (a consequence of boundedness, needed for the norm on $C(\bar D)$). Nonemptiness of $D$ is added: the page's $\max_{x\in\bar D}$ needs it, and for $D=\emptyset$ Lean's supremum over the empty type is $0$. $A^{-1}$ is a continuous linear map `Ainv` together with the hypothesis `hA` that `Ainv F` is, on $\bar D$, a weak solution `IsDirichletSol D F y` for every $F\in L^2(D)$; Lemma 1.2 shows such a map exists and its uniqueness clause makes it the paper's $A^{-1}$. The Clarke directional derivative is the page-3 limsup with denominator $t$ (the page prints $h$, a misprint), and the dual of $L^2(D)$ is identified with $L^2(D)$ through the inner product, as on p. 11. $\Sigma^{1/2}$ is the positive semidefinite square root `CFC.sqrt Sigma`, the root used by Mathlib's `multivariateGaussian`. The integral is the Aumann integral over the restriction of $\mu_\zeta$ to $\{\rho(\bar u,v)<\infty\}$ (not renormalized), and the minus sign is the pointwise negative of that set.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 14, Theorem 2.15

import Mathlib
import Definitions.Def_ChanceStateCtrl_PDE_Setting
import Definitions.Def_ChanceStateCtrl_PDE_Model

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal Pointwise

namespace ChanceStateCtrl.PDE

/-- Theorem 2.15 (p. 14): under (26) at `ū`, `φ` is locally Lipschitzian around `ū` and
`∂^C φ(ū) ⊆ -∫_{ρ(ū, v) < ∞} χ(ρ(ū, v)) · clco{ … } dμ_ζ(v)` (40), with equality when `M*(ū, v)`
is a singleton for `μ_ζ`-a.e. `v` with `ρ(ū, v) < ∞` or the set (11) is bounded. -/
theorem theorem_2_15 {d m : ℕ} (D : Set (EuclideanSpace ℝ (Fin d)))
    (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D) (hDne : D.Nonempty)
    (hd : d = 1 ∨ d = 2 ∨ d = 3) (hDS : IsClassS D)
    [CompactSpace (closure D)] (Ainv : L2 D →L[ℝ] C(closure D, ℝ))
    (hA : ∀ F : L2 D, ∃ y, IsDirichletSol D (⇑F) y ∧ ∀ x : closure D, Ainv F x = y x)
    (f₀ : L2 D) (φ : Fin m → L2 D) (α : ℝ)
    (hm : 0 < m) (Sigma : Matrix (Fin m) (Fin m) ℝ) (hSigma : Sigma.PosDef)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (hξlaw : P.map ξ = multivariateGaussian 0 Sigma)
    (ubar : L2 D) (h26 : ∀ x : closure D, stateS Ainv f₀ φ ubar 0 x < α) :
    LocLipschitzAt (probFn P ξ (gPDE Ainv f₀ φ α)) ubar ∧
    clarkeSubdiffL2 (probFn P ξ (gPDE Ainv f₀ φ α)) ubar ⊆ -integralSet Ainv f₀ φ α Sigma ubar ∧
    (EqCond Ainv f₀ φ α Sigma ubar → clarkeSubdiffL2 (probFn P ξ (gPDE Ainv f₀ φ α)) ubar = -integralSet Ainv f₀ φ α Sigma ubar) := by sorry

end ChanceStateCtrl.PDE
