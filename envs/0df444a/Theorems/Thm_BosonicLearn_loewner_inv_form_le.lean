-- Prove2me | Theorems.Thm_BosonicLearn_loewner_inv_form_le
-- name    : BosonicLearn.loewner_inv_form_le
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T06:58:47.576614+00:00
-- url     : https://prove2.me/theorems/47d9e147-bf62-45c7-ba9d-ba17f6230590
-- title:
--   $A\preceq\alpha B\ \Rightarrow\ v^{T}B^{-1}v\le\alpha\,v^{T}A^{-1}v$ for positive definite $A,B$
-- statement:
--   Inversion reverses the Loewner order, in quadratic-form version.
--
--   Let $A,B$ be real positive definite matrices of the same size and $\alpha>0$ with $A\preceq\alpha B$. Then for every real vector $v$,
--
--   $$
--   v^{\top}B^{-1}v\;\le\;\alpha\;v^{\top}A^{-1}v ,\qquad\text{i.e.}\qquad \|B^{-1/2}v\|_2\le\sqrt\alpha\,\|A^{-1/2}v\|_2 .
--   $$
--
--   Role. In the proof of Theorem 8, $A=C=\Sigma+\tfrac12\mathbf 1$ is the covariance of the heterodyne outcomes, $B=\Sigma$ and $\alpha=\alpha_\nu$: the concentration of $\hat\mu$ in the $C^{-1}$ norm (Eq. (210)) gives the bound in the $\Sigma^{-1}$ norm needed by Lemma 18.
--
--   **Formalization Note** The quadratic forms are `v ⬝ᵥ (B⁻¹ *ᵥ v)`; Loewner order is `Matrix.PosSemidef` of the difference. Pure linear algebra.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, p. 62, between Eqs. (216) and (217) ("inversion reverses the positive-semidefinite order", proof of Theorem 8)

import Mathlib

open scoped Matrix

namespace BosonicLearn

/-- **Inversion reverses the Loewner order (quadratic-form version).**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §7.2, proof of Theorem 8, p. 62: "From C ⪯ α_ν Σ, inversion reverses the positive-semidefinite order, so
C^{−1} ⪰ α_ν^{−1} Σ^{−1}, or equivalently Σ^{−1} ⪯ α_ν C^{−1}. Consequently,
‖Σ^{−1/2}(µ̂ − µ)‖₂ ≤ √α_ν ‖C^{−1/2}(µ̂ − µ)‖₂."

Let `A, B` be real positive definite matrices with `A ⪯ α B`, `α > 0`. Then for every vector `v`,
`vᵀ B⁻¹ v ≤ α · vᵀ A⁻¹ v`.

**Formalization Note.** `‖M^{−1/2} v‖₂² = vᵀ M⁻¹ v` for positive definite `M`; Loewner order is positive
semidefiniteness of the difference. -/
theorem loewner_inv_form_le {ι : Type} [Fintype ι] [DecidableEq ι] (A B : Matrix ι ι ℝ) (hA : A.PosDef)
    (hB : B.PosDef) (α : ℝ) (hα : 0 < α) (hAB : (α • B - A).PosSemidef) (v : ι → ℝ) :
    v ⬝ᵥ (B⁻¹ *ᵥ v) ≤ α * (v ⬝ᵥ (A⁻¹ *ᵥ v)) := by sorry

end BosonicLearn
