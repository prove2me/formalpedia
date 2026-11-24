-- Prove2me | Theorems.Thm_DSReg_componentwise_identifiability
-- name    : DSReg.componentwise_identifiability
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:29:30.666688+00:00
-- url     : https://prove2.me/theorems/7e15cfdf-6519-4d7c-b757-ea28078c2668
-- title:
--   Theorem 2: component-wise identifiability without reconstruction
-- statement:
--   Let $\mu$ be the law of the world latent $z\in\mathbb{R}^d$ and $x=g(z)\in\mathbb{R}^p$, with $g$ differentiable $\mu$-a.e. and measurable dependency Jacobian $D=\partial x/\partial z$. Let $h$ be a measurable representation with $h(z)=Qz$ $\mu$-a.s. for some $Q\in O(d)$, as in Lemma 1. Assume Structural Diversity (the footprints $\mathcal S_i$ are pairwise distinct) and Functional no-cancellation. Let $R\in O(d)$ minimize the support-sparsity criterion
--
--   $$\min_{R\in O(d)}\Big\|\frac{\partial x}{\partial\tilde z}\Big\|_{0,\mu},\qquad\tilde z=Rh(z).$$
--
--   Then $RQ$ is a signed permutation. Equivalently, there are a permutation $\pi$ of $[d]$ and signs $s_1,\dots,s_d\in\{\pm1\}$ with
--
--   $$\tilde z_i=s_iz_{\pi(i)}\quad\mu\text{-a.s. for every }i\in[d].$$
--
--   So DSReg recovers every individual world latent up to sign and relabeling, without reconstruction.
--
--   **Formalization Note** $\partial x/\partial\tilde z$ is the Jacobian of $\tilde z\mapsto g(Q^\top R^\top\tilde z)$ at $\tilde z=RQz$, as in Lemma 1. $\mu$ is any probability measure on $\mathbb{R}^d$: the paper writes "$\mu$ is the law of $z$ (standard Gaussian under Theorem 1)", and Gaussianity enters only through the premise $h(z)=Qz$, which is a hypothesis here.
-- source:
--   Zheng, Klindt, Balestriero and Schölkopf, DSReg: Provably Recovering Individual World Latents without Reconstruction, arXiv:2610.09457v1 (2026), Section 3.2, Theorem 2, eq. (3), p. 5; proof in Appendix A.2, pp. 19-20

import Mathlib
import Definitions.Def_DSReg_Basic

open MeasureTheory

namespace DSReg

theorem componentwise_identifiability {d p : ℕ} (μ : Measure (Fin d → ℝ))
    [IsProbabilityMeasure μ] (g : (Fin d → ℝ) → Fin p → ℝ)
    (hdiff : ∀ᵐ z ∂μ, DifferentiableAt ℝ g z) (hmeas : ∀ r i, Measurable fun z => depJac g z r i)
    (h : (Fin d → ℝ) → Fin d → ℝ) (hhm : Measurable h) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin d) ℝ) (hh : ∀ᵐ z ∂μ, h z = Q.mulVec z)
    (hsd : StructuralDiversity (footprint μ (depJac g)))
    (hfnc : FunctionalNoCancellation μ (depJac g))
    (R : Matrix (Fin d) (Fin d) ℝ) (hR : IsSupportMinimizer μ g Q R) :
    IsSignedPerm (R * Q) ∧ RecoversLatents μ (fun z => R.mulVec (h z)) := by sorry

end DSReg
