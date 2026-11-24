-- Prove2me | Theorems.Thm_DSReg_dependency_bridge
-- name    : DSReg.dependency_bridge
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-24T04:27:11.555798+00:00
-- url     : https://prove2.me/theorems/af04fa9a-93a1-490a-9657-4a7fb95956f5
-- title:
--   Lemma 1: dependency bridge
-- statement:
--   Let $\mu$ be the law of the world latent $z\in\mathbb{R}^d$, and let $x=g(z)\in\mathbb{R}^p$, where $g$ is differentiable $\mu$-almost everywhere with measurable dependency Jacobian $D(z)=\partial x/\partial z$. Suppose the representation is linearly identifiable with orthogonal ambiguity: $h(z)=Qz$ $\mu$-a.s. for some $Q\in O(d)$. Then for candidate latents $\tilde z=Rh(z)$ with $R\in O(d)$,
--
--   $$\frac{\partial x}{\partial\tilde z}=D(z)\,Q^\top R^\top\qquad\text{for }\mu\text{-a.e. }z.$$
--
--   The ambiguity therefore enters the dependency structure as right multiplication by the orthogonal matrix $U=Q^\top R^\top$.
--
--   **Formalization Note** $\partial x/\partial\tilde z$ is the Jacobian of $\tilde z\mapsto g(Q^\top R^\top\tilde z)$ at $\tilde z=RQz$, the map the paper obtains from the premise $z=Q^\top R^\top\tilde z$. The identity is stated $\mu$-a.e. in $z$, as in the paper. Because the premise is built into this definition, it in fact holds at every $z$ for every $g$ (both sides are $0$ where $g$ is not differentiable), and the hypotheses on $\mu$, $g$ and $h$ are not needed.
-- source:
--   Zheng, Klindt, Balestriero and Schölkopf, DSReg: Provably Recovering Individual World Latents without Reconstruction, arXiv:2610.09457v1 (2026), Section 3.2, Lemma 1, eq. (2), p. 5; proof in Appendix A.1, p. 14

import Mathlib
import Definitions.Def_DSReg_Basic

open MeasureTheory

namespace DSReg

theorem dependency_bridge {d p : ℕ} (μ : Measure (Fin d → ℝ)) [IsProbabilityMeasure μ]
    (g : (Fin d → ℝ) → Fin p → ℝ) (hdiff : ∀ᵐ z ∂μ, DifferentiableAt ℝ g z)
    (hmeas : ∀ r i, Measurable fun z => depJac g z r i)
    (h : (Fin d → ℝ) → Fin d → ℝ) (Q : Matrix (Fin d) (Fin d) ℝ)
    (hQ : Q ∈ Matrix.orthogonalGroup (Fin d) ℝ) (hh : ∀ᵐ z ∂μ, h z = Q.mulVec z)
    (R : Matrix (Fin d) (Fin d) ℝ) (hR : R ∈ Matrix.orthogonalGroup (Fin d) ℝ) :
    ∀ᵐ z ∂μ, candJac g Q R z = depJac g z * Q.transpose * R.transpose := by sorry

end DSReg
