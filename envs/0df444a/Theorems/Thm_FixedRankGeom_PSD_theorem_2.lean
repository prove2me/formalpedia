-- Prove2me | Theorems.Thm_FixedRankGeom_PSD_theorem_2
-- name    : FixedRankGeom.PSD.theorem_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:37:34.829306+00:00
-- url     : https://prove2.me/theorems/7e16269d-de3c-4c81-8dde-47a67fe5d269
-- title:
--   Theorem 2, p. 10 — sandwich inequalities for spectra of Hessians
-- statement:
--   Let $V\le E$ and $T\le F$ be subspaces of real vector spaces with $\dim V=\dim T=d$. Let $g_V$ (on $E$) and $g_T$ (on $F$) be symmetric bilinear forms, positive on $V\setminus\{0\}$ and $T\setminus\{0\}$ respectively, and let $H_V$, $H_T$ be symmetric bilinear forms (playing the role of $\overline{\operatorname{Hess} h([Z])}$ and $\operatorname{Hess} f(X)$). Let $\mathcal L:E\to F$ be linear and restrict to a bijection $V\to T$ with
--   $$H_V(\theta,\theta)=H_T(\mathcal L\theta,\mathcal L\theta)\quad\forall\theta\in V\qquad(12)$$
--   and, for some $0\le\alpha\le\beta$,
--   $$\alpha\,g_V(\theta,\theta)\le g_T(\mathcal L\theta,\mathcal L\theta)\le\beta\,g_V(\theta,\theta)\quad\forall\theta\in V.\qquad(13)$$
--   Then for $k=1,\dots,d$, $\lambda_k(H_V)$ is sandwiched between $\alpha\lambda_k(H_T)$ and $\beta\lambda_k(H_T)$:
--   $$\min\{\alpha\lambda_k(H_T),\beta\lambda_k(H_T)\}\le\lambda_k(H_V)\le\max\{\alpha\lambda_k(H_T),\beta\lambda_k(H_T)\},$$
--   where $\lambda_k$ is the $k$-th largest eigenvalue of the form relative to its metric, i.e. the max–min value $\max_{\dim C=k}\min_{u\in C\setminus0}H(u,u)/g(u,u)$ over $k$-dimensional subspaces $C$.
--
--   This abstract comparison is the final step of the paper's general procedure: once a Hessian identity (12) and metric distortion bounds (13) are established, eigenvalues and in particular their signs transfer between geometries.
--
--   **Formalization Note** The paper's statement "both Hessians have $d$ eigenvalues" is encoded by $\dim V=\dim T=d$ and the restriction $1\le k\le d$. The paper's $\mathcal L$ is linear in every application; the abstract statement assumes linearity. "Sandwiched" is read with $\min/\max$ because the order of the bounds flips when $\lambda_k(H_T)<0$. In (12)–(13) the printed domain "$\theta_Z\in\mathcal H_X\bar{\mathcal M}^q$" is read as $\mathcal H_Z\bar{\mathcal M}^q$, the domain of $\mathcal L$.
-- source:
--   Luo, Li & Zhang, On Geometric Connections of Embedded and Quotient Geometries in Riemannian Fixed-rank Matrix Optimization, arXiv:2110.12121v2, p. 10, Theorem 2, (12)–(13); Lemma 13 p. 54

import Mathlib
import Definitions.Def_FixedRankGeom_PSD_Model

open scoped RealInnerProductSpace Matrix ContDiff
open ProjLikeRetr.Retractor

namespace FixedRankGeom.PSD

/-- Theorem 2, p. 10: sandwich inequalities for the spectra of two quadratic forms related by a linear
bijection with bounded distortion of the metrics. -/
theorem theorem_2 {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (V : Submodule ℝ E) (T : Submodule ℝ F) (d : ℕ)
    (hV : Module.finrank ℝ V = d) (hT : Module.finrank ℝ T = d)
    (gV : LinearMap.BilinForm ℝ E) (hgVs : ∀ x y, gV x y = gV y x)
    (hgVp : ∀ v ∈ V, v ≠ 0 → 0 < gV v v)
    (gT : LinearMap.BilinForm ℝ F) (hgTs : ∀ x y, gT x y = gT y x)
    (hgTp : ∀ v ∈ T, v ≠ 0 → 0 < gT v v)
    (HV : LinearMap.BilinForm ℝ E) (hHVs : ∀ x y, HV x y = HV y x)
    (HT : LinearMap.BilinForm ℝ F) (hHTs : ∀ x y, HT x y = HT y x)
    (L : E →ₗ[ℝ] F) (hL : Set.BijOn L V T)
    (h12 : ∀ θ ∈ V, HV θ θ = HT (L θ) (L θ))
    (α β : ℝ) (hα : 0 ≤ α) (hαβ : α ≤ β)
    (h13 : ∀ θ ∈ V, α * gV θ θ ≤ gT (L θ) (L θ) ∧ gT (L θ) (L θ) ≤ β * gV θ θ) :
    ∀ k, 1 ≤ k → k ≤ d →
      IsSandwiched (kthEig (fun a b => gV a b) (fun v => HV v v) V k)
        (α * kthEig (fun a b => gT a b) (fun v => HT v v) T k)
        (β * kthEig (fun a b => gT a b) (fun v => HT v v) T k) := by sorry

end FixedRankGeom.PSD
