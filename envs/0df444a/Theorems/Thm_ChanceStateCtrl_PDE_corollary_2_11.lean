-- Prove2me | Theorems.Thm_ChanceStateCtrl_PDE_corollary_2_11
-- name    : ChanceStateCtrl.PDE.corollary_2_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T01:21:32.473703+00:00
-- url     : https://prove2.me/theorems/9144e64e-2ee0-4d6f-8e06-956d54a1fbe6
-- title:
--   Corollary 2.11, p. 10 — under (26) the conclusions of Theorem 2.2 hold for (24)
-- statement:
--   Throughout, $D\subseteq\mathbb R^d$ ($d\in\{1,2,3\}$) is a nonempty, open, bounded domain of class S, $A^{-1}:L^2(D)\to C(\bar D)$ is the solution operator of the Dirichlet problem $-\Delta y=F$ in $D$, $y=0$ on $\partial D$ (in $H^1_0(D)\cap C(\bar D)$), $f_0,\varphi_1,\dots,\varphi_m\in L^2(D)$, and $S(u,z)=A^{-1}(u+f_0+\sum_i z_i\varphi_i)$, $P(u,z)=A^{-1}u+\sum_i z_iA^{-1}\varphi_i$ are the operators of (5). The constraint function of (24) is $g(u,z)=\max_{x\in\bar D}[S(u,z)](x)-\alpha$ for a threshold $\alpha\in\mathbb R$.
--
--   The random vector $\xi:\Omega\to\mathbb R^m$ ($m\ge1$) on a probability space $(\Omega,\mathcal F,\mathbb P)$ is measurable with law $\mathcal N(0,\Sigma)$, $\Sigma$ positive definite, and $\varphi(u)=\mathbb P(\omega\mid g(u,\xi(\omega))\le0)$ is the probability function of (24).
--
--   Fix $\bar u\in L^2(D)$ whose expected state $\bar y=S(\bar u,0)$ satisfies
--   $$\bar y(x)<\alpha\qquad\forall x\in\bar D.\tag{26}$$
--   Then the conclusions of Theorem 2.2 hold:
--
--   1. the partial radial probability functions $e(\cdot,v)$, $v\in\mathbb S^{m-1}$, are uniformly locally Lipschitzian around $\bar u$ (one neighbourhood and one constant for all $v$);
--   2. $\varphi$ is locally Lipschitzian around $\bar u$;
--   3. $\displaystyle\partial^C\varphi(\bar u)\subseteq\int_{\mathbb S^{m-1}}\partial^C_ue(\bar u,v)\,d\mu_\zeta(v)$ (15), an Aumann integral;
--   4. if $\mu_\zeta\{v\mid\#\partial^C_ue(\bar u,v)\ge2\}=0$ (16), then $\partial^C\varphi(\bar u)=\{y\}$ is a singleton, equality holds in (15), and $\varphi$ is strictly differentiable at $\bar u$: $\lim_{u'\to\bar u,t\downarrow0}(\varphi(u'+th)-\varphi(u'))/t=(y,h)_{L^2(D)}$ for every $h$.
--
--   Theorem 2.2 (p. 5, from [22]) reads: "In addition to Assumption 2.1, let (10) and (12) be satisfied at some $\bar u\in U$ … Then, the partial radial probability functions $e(\cdot,v)$, $v\in\mathbb S^{m-1}$, are uniformly locally Lipschitzian around $\bar u$ with a Lipschitz constant independent of $v$. Moreover, the (total) probability function $\varphi$ is locally Lipschitzian around $\bar u$ and its Clarke subdifferential at $\bar u$ can be estimated from above by (15) … If, in addition, the condition (16) is satisfied, then the Clarke subdifferential of $\varphi$ at $\bar u$ reduces to a singleton and equality holds in (15). As a consequence, $\varphi$ is strictly differentiable at $\bar u$ in the Hadamard sense."
--
--   **Formalization Note** The domain hypotheses are binders: `IsOpen D`, `Bornology.IsBounded D`, `D.Nonempty`, `d = 1 ∨ d = 2 ∨ d = 3`, `IsClassS D`, and `[CompactSpace (closure D)]` (a consequence of boundedness, needed for the norm on $C(\bar D)$). Nonemptiness of $D$ is added: the page's $\max_{x\in\bar D}$ needs it, and for $D=\emptyset$ Lean's supremum over the empty type is $0$. $A^{-1}$ is a continuous linear map `Ainv` together with the hypothesis `hA` that `Ainv F` is, on $\bar D$, a weak solution `IsDirichletSol D F y` for every $F\in L^2(D)$; Lemma 1.2 shows such a map exists and its uniqueness clause makes it the paper's $A^{-1}$. The Clarke directional derivative is the page-3 limsup with denominator $t$ (the page prints $h$, a misprint), and the dual of $L^2(D)$ is identified with $L^2(D)$ through the inner product, as on p. 11. $\Sigma^{1/2}$ is the positive semidefinite square root `CFC.sqrt Sigma`, the root used by Mathlib's `multivariateGaussian`. "$\#\partial^C_ue(\bar u,v)\ge2$ on a null set" is stated as "$\partial^C_ue(\bar u,v)$ is a subsingleton for $\mu_\zeta$-a.e. $v$". Strict Hadamard differentiability is stated as strict differentiability in every direction; for a locally Lipschitz function the uniformity on compact sets of directions is automatic.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 10, Corollary 2.11 (with Theorem 2.2, p. 5, stated in this paper, citing [22])

import Mathlib
import Definitions.Def_ChanceStateCtrl_PDE_Setting
import Definitions.Def_ChanceStateCtrl_PDE_Model

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal Pointwise

namespace ChanceStateCtrl.PDE

/-- Corollary 2.11 (p. 10): if the expected state `ȳ = S(ū, 0)` satisfies (26), the conclusions of
Theorem 2.2 hold for (24): the partial radial probability functions `e(·, v)` are uniformly locally
Lipschitzian around `ū` with a constant independent of `v`, `φ` is locally Lipschitzian around `ū`,
the inclusion (15) holds, and under (16) `∂^C φ(ū)` is a singleton, (15) is an equality, and `φ` is
strictly (Hadamard) differentiable at `ū`. -/
theorem corollary_2_11 {d m : ℕ} (D : Set (EuclideanSpace ℝ (Fin d)))
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
    (∃ K, ∃ t ∈ 𝓝 ubar, ∀ v : Metric.sphere (0 : EuclideanSpace ℝ (Fin m)) 1,
      LipschitzOnWith K (fun u => radialProb (gPDE Ainv f₀ φ α) Sigma u v) t) ∧
    LocLipschitzAt (probFn P ξ (gPDE Ainv f₀ φ α)) ubar ∧
    clarkeSubdiffL2 (probFn P ξ (gPDE Ainv f₀ φ α)) ubar ⊆
      aumannL2 (sphereLaw m) (fun v => clarkeSubdiffL2 (fun u => radialProb (gPDE Ainv f₀ φ α) Sigma u v) ubar) ∧
    ((∀ᵐ v ∂(sphereLaw m), (clarkeSubdiffL2 (fun u => radialProb (gPDE Ainv f₀ φ α) Sigma u v) ubar).Subsingleton) →
      ∃ y : L2 D, clarkeSubdiffL2 (probFn P ξ (gPDE Ainv f₀ φ α)) ubar = {y} ∧
        clarkeSubdiffL2 (probFn P ξ (gPDE Ainv f₀ φ α)) ubar =
          aumannL2 (sphereLaw m) (fun v => clarkeSubdiffL2 (fun u => radialProb (gPDE Ainv f₀ φ α) Sigma u v) ubar) ∧
        ∀ h : L2 D, Tendsto (fun q : L2 D × ℝ => (probFn P ξ (gPDE Ainv f₀ φ α) (q.1 + q.2 • h) - probFn P ξ (gPDE Ainv f₀ φ α) q.1) / q.2)
          (𝓝 ubar ×ˢ 𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ y h))) := by sorry

end ChanceStateCtrl.PDE
