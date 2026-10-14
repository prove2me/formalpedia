-- Prove2me | Theorems.Thm_ChanceStateCtrl_PDE_lemma_2_14
-- name    : ChanceStateCtrl.PDE.lemma_2_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:42.637173+00:00
-- url     : https://prove2.me/theorems/e9cf201a-816a-4bbf-bc88-30d4635d3ad1
-- title:
--   Lemma 2.14, p. 12 — under (26), ρ(ū, v) < ∞ gives ∂ᶜ_u e(ū, v) = −χ(ρ(ū, v))·clco{u_x / [P(0, Σ^{1/2}v)](x) | x ∈ M*(ū, v)}
-- statement:
--   Throughout, $D\subseteq\mathbb R^d$ ($d\in\{1,2,3\}$) is a nonempty, open, bounded domain of class S, $A^{-1}:L^2(D)\to C(\bar D)$ is the solution operator of the Dirichlet problem $-\Delta y=F$ in $D$, $y=0$ on $\partial D$ (in $H^1_0(D)\cap C(\bar D)$), $f_0,\varphi_1,\dots,\varphi_m\in L^2(D)$, and $S(u,z)=A^{-1}(u+f_0+\sum_i z_i\varphi_i)$, $P(u,z)=A^{-1}u+\sum_i z_iA^{-1}\varphi_i$ are the operators of (5). The constraint function of (24) is $g(u,z)=\max_{x\in\bar D}[S(u,z)](x)-\alpha$ for a threshold $\alpha\in\mathbb R$.
--
--   Let $\Sigma$ be positive definite ($m\ge1$). Fix $\bar u\in L^2(D)$ with (26). If $v\in\mathbb S^{m-1}$ satisfies $\rho(\bar u,v)<\infty$, then
--   $$\partial^C_ue(\bar u,v)=-\chi(\rho(\bar u,v))\cdot\operatorname{clco}\Big\{\frac{1}{[P(0,\Sigma^{1/2}v)](x)}\,u_x\ \Big|\ x\in M^*(\bar u,v)\Big\},$$
--   where $M^*(\bar u,v)=\{x\in\bar D\mid[P(0,\Sigma^{1/2}v)](x)>0,\ \bar y(x)+\rho(\bar u,v)[P(0,\Sigma^{1/2}v)](x)=\alpha\}$, $u_x\in L^2(D)$ is defined by $(u_x,h)_{L^2(D)}=[P(h,0)](x)=(A^{-1}h)(x)$, and $\chi$ is the chi density with $m$ degrees of freedom.
--
--   This is the explicit formula for the partial subdifferential of the radial probability function in terms of the problem data; integrated over the sphere it gives (40).
--
--   **Formalization Note** The domain hypotheses are binders: `IsOpen D`, `Bornology.IsBounded D`, `D.Nonempty`, `d = 1 ∨ d = 2 ∨ d = 3`, `IsClassS D`, and `[CompactSpace (closure D)]` (a consequence of boundedness, needed for the norm on $C(\bar D)$). Nonemptiness of $D$ is added: the page's $\max_{x\in\bar D}$ needs it, and for $D=\emptyset$ Lean's supremum over the empty type is $0$. $A^{-1}$ is a continuous linear map `Ainv` together with the hypothesis `hA` that `Ainv F` is, on $\bar D$, a weak solution `IsDirichletSol D F y` for every $F\in L^2(D)$; Lemma 1.2 shows such a map exists and its uniqueness clause makes it the paper's $A^{-1}$. The Clarke directional derivative is the page-3 limsup with denominator $t$ (the page prints $h$, a misprint), and the dual of $L^2(D)$ is identified with $L^2(D)$ through the inner product, as on p. 11. $\Sigma^{1/2}$ is the positive semidefinite square root `CFC.sqrt Sigma`, the root used by Mathlib's `multivariateGaussian`. clco is the norm closure of the convex hull in $L^2(D)$ (equal to the weak closure by Mazur's theorem). The scalar $-\chi(\rho)$ multiplies the set pointwise.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 12, Lemma 2.14

import Mathlib
import Definitions.Def_ChanceStateCtrl_PDE_Setting
import Definitions.Def_ChanceStateCtrl_PDE_Model

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal Pointwise

namespace ChanceStateCtrl.PDE

/-- Lemma 2.14 (p. 12): under (26) at `ū`, if `ρ(ū, v) < ∞` then
`∂^C_u e(ū, v) = -χ(ρ(ū, v)) · clco{ [P(0, Σ^{1/2}v)](x)⁻¹ · u_x | x ∈ M*(ū, v) }`. -/
theorem lemma_2_14 {d m : ℕ} (D : Set (EuclideanSpace ℝ (Fin d)))
    (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D) (hDne : D.Nonempty)
    (hd : d = 1 ∨ d = 2 ∨ d = 3) (hDS : IsClassS D)
    [CompactSpace (closure D)] (Ainv : L2 D →L[ℝ] C(closure D, ℝ))
    (hA : ∀ F : L2 D, ∃ y, IsDirichletSol D (⇑F) y ∧ ∀ x : closure D, Ainv F x = y x)
    (f₀ : L2 D) (φ : Fin m → L2 D) (α : ℝ)
    (hm : 0 < m) (Sigma : Matrix (Fin m) (Fin m) ℝ) (hSigma : Sigma.PosDef)
    (ubar : L2 D) (h26 : ∀ x : closure D, stateS Ainv f₀ φ ubar 0 x < α)
    (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1)
    (hv : radius (gPDE Ainv f₀ φ α) Sigma ubar v < ⊤) :
    clarkeSubdiffL2 (fun u => radialProb (gPDE Ainv f₀ φ α) Sigma u v) ubar =
      (-(chiDensity m (radius (gPDE Ainv f₀ φ α) Sigma ubar v).toReal)) •
        Kset Ainv f₀ φ α Sigma ubar v := by sorry

end ChanceStateCtrl.PDE
