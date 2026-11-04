-- Prove2me | Theorems.Thm_ChanceStateCtrl_PDE_theorem_2_4_bounded
-- name    : ChanceStateCtrl.PDE.theorem_2_4_bounded
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-11-03T12:27:52.612822+00:00
-- url     : https://prove2.me/theorems/60240947-ec58-4958-a5cd-177aa648da5b
-- title:
--   Theorem 2.4 for (24) — exact formula $\partial^C\varphi(\bar u)=\int\partial^C_u e(\bar u,v)\,d\mu_\zeta(v)$ when the set (11) is bounded
-- statement:
--   Let $D\subseteq\mathbb R^d$ ($d\in\{1,2,3\}$) be a nonempty, open, bounded domain of class S, let $A^{-1}:L^2(D)\to C(\bar D)$ be the solution operator of the Dirichlet problem $-\Delta y=F$ in $D$, $y=0$ on $\partial D$, and let $f_0,\varphi_1,\dots,\varphi_m\in L^2(D)$, $\alpha\in\mathbb R$. With $S(u,z)=A^{-1}(u+f_0+\sum_i z_i\varphi_i)$, the constraint function of problem (24) is
--   $$g(u,z)=\max_{x\in\bar D}[S(u,z)](x)-\alpha .$$
--   Let $\xi\sim\mathcal N(0,\Sigma)$ on a probability space, $\Sigma$ positive definite ($m\ge1$), let $\varphi(u)=\mathbb P(g(u,\xi)\le0)$ be the probability function and $e(u,v)=\mu_\eta\{r\ge0\mid g(u,r\Sigma^{1/2}v)\le0\}$ ($v\in\mathbb S^{m-1}$) the radial probability function (13), where $\mu_\eta$ is the chi law with $m$ degrees of freedom.
--
--   Fix $\bar u\in L^2(D)$ whose expected state satisfies (26): $[S(\bar u,0)](x)<\alpha$ for all $x\in\bar D$ (this is condition (10), $g(\bar u,0)<0$). Assume moreover that the set
--   $$M=\{z\in\mathbb R^m\mid g(\bar u,z)\le0\}\tag{11}$$
--   is bounded. Then the Clarke subdifferential of $\varphi$ at $\bar u$ is given exactly by the Aumann integral
--   $$\partial^C\varphi(\bar u)=\int_{\mathbb S^{m-1}}\partial^C_u e(\bar u,v)\,d\mu_\zeta(v),$$
--   where $\mu_\zeta$ is the uniform distribution on the sphere.
--
--   This is Theorem 2.4 of the paper specialized to problem (24): $g$ is jointly convex (Lemma 2.9), (26) gives (10), and $M$ is bounded, so the assumptions of Lemma 2.3 hold. It is the case "the set (11) is bounded" of the equality statement in Theorem 2.15, p. 14 ("implying the assumptions of Lemma 2.3").
--
--   **Formalization note.** Same conventions as Theorem 2.15 of this mission: $H^*$ is identified with $L^2(D)$ through the inner product, the Clarke subdifferential is `clarkeSubdiffL2`, and the Aumann integral is `aumannL2` over `sphereLaw m`.
-- source:
--   Geiersbach & Henrion, Optimality conditions in control problems with random state constraints in probabilistic or almost-sure form, arXiv:2306.03965v2, p. 7, Theorem 2.4 (with Lemma 2.3, p. 6), applied to problem (24) as invoked in Theorem 2.15, p. 14

import Mathlib
import Definitions.Def_ChanceStateCtrl_PDE_Setting
import Definitions.Def_ChanceStateCtrl_PDE_Model

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal Pointwise

namespace ChanceStateCtrl.PDE

/-- Theorem 2.4 (p. 7) for problem (24), as invoked in Theorem 2.15 (p. 14): under (26) at `ū`,
if the set `M = {z | g(ū, z) ≤ 0}` of (11) is bounded, then (Lemma 2.3's assumptions hold, since
`g` is jointly convex by Lemma 2.9 and (26) is (10)) the exact formula
`∂^C φ(ū) = ∫_{S^{m-1}} ∂^C_u e(ū, v) dμ_ζ(v)` holds. -/
theorem theorem_2_4_bounded {d m : ℕ} (D : Set (EuclideanSpace ℝ (Fin d)))
    (hDopen : IsOpen D) (hDbdd : Bornology.IsBounded D) (hDne : D.Nonempty)
    (hd : d = 1 ∨ d = 2 ∨ d = 3) (hDS : IsClassS D)
    [CompactSpace (closure D)] (Ainv : L2 D →L[ℝ] C(closure D, ℝ))
    (hA : ∀ F : L2 D, ∃ y, IsDirichletSol D (⇑F) y ∧ ∀ x : closure D, Ainv F x = y x)
    (f₀ : L2 D) (φ : Fin m → L2 D) (α : ℝ)
    (hm : 0 < m) (Sigma : Matrix (Fin m) (Fin m) ℝ) (hSigma : Sigma.PosDef)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ξ : Ω → EuclideanSpace ℝ (Fin m)) (hξ : Measurable ξ)
    (hξlaw : P.map ξ = multivariateGaussian 0 Sigma)
    (ubar : L2 D) (h26 : ∀ x : closure D, stateS Ainv f₀ φ ubar 0 x < α)
    (hM : Bornology.IsBounded {z : EuclideanSpace ℝ (Fin m) | gPDE Ainv f₀ φ α ubar z ≤ 0}) :
    clarkeSubdiffL2 (probFn P ξ (gPDE Ainv f₀ φ α)) ubar =
      aumannL2 (sphereLaw m)
        (fun v => clarkeSubdiffL2 (fun u => radialProb (gPDE Ainv f₀ φ α) Sigma u v) ubar) := by sorry

end ChanceStateCtrl.PDE
