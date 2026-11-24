-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_Supplement_theorem_14_1
-- name    : ConjGrad.ErrorDecrease.Supplement.theorem_14_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:03:54.938154+00:00
-- url     : https://prove2.me/theorems/91b1405f-4ede-41bd-be54-4ef1c27566c8
-- title:
--   Theorem 14:1 — the polynomial–vector correspondence is an isometry
-- statement:
--   Let $m(\lambda)$ be a mass distribution on $[0,l]$ related to an $n\times n$ matrix $A$ and a vector $r_0$ as in §14 (Gauss nodes $\lambda_j$, weights $m_j>0$, orthonormal eigenvectors $e_j$, $r_0=\sum\alpha_je_j$, $\alpha_j^2=m_j$). Metrize the polynomials of degree at most $n-1$ by $\|R\|=\left[\int_0^lR(\lambda)^2dm(\lambda)\right]^{1/2}$. Then the correspondence $R\mapsto r=R(A)r_0$ is isometric:
--
--   $$\int_0^lR(\lambda)R'(\lambda)\,dm(\lambda)=(r,r')$$
--
--   for all polynomials $R,R'$ of degree at most $n-1$ with corresponding vectors $r,r'$.
--
--   The isometry transports orthogonal polynomials of $m$ to orthogonal vectors in $\mathbb R^n$, which is how the cg residuals arise from orthogonal polynomials.
--
--   **Formalization Note** The mass distribution is its Lebesgue–Stieltjes measure $\mu$ on $[0,l]$ (`IsSpectralModel μ l A r₀`), so $\int_0^l\cdot\,dm$ is the Bochner integral against $\mu$; `polyVec A r₀ R` is $R(A)r_0$.
--
--   Differences from the source:
--   - generalization: $A$ positive definite with the Gauss nodes as eigenvalues; $m$ of type (a) or (b) → any matrix and mass distribution satisfying the relation `IsSpectralModel`; reason: every configuration of §14 satisfies the relation, so the statement specializes to the source's
--   - encoding: $\deg R\le n-1$ → `R.degree < n`; reason: same polynomials; avoids natural-number subtraction at $n=0$
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 429, Theorem 14:1 (PDF p. 21)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_IsSpectralModel

open Matrix MeasureTheory

namespace ConjGrad.ErrorDecrease.Supplement

/-- Theorem 14:1 (Hestenes–Stiefel 1952, p. 429): for a mass distribution related to `A` and `r₀` as
in §14, the correspondence `R ↦ R(A)r₀` is an isometry from the polynomials of degree at most
`n − 1` with the inner product `∫₀ˡ R R' dm` to `ℝⁿ` with the Euclidean inner product. -/
theorem theorem_14_1 {n : ℕ} (μ : Measure ℝ) (l : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (r₀ : Fin n → ℝ) (hrel : IsSpectralModel μ l A r₀) (R R' : Polynomial ℝ)
    (hR : R.degree < n) (hR' : R'.degree < n) :
    ∫ t, R.eval t * R'.eval t ∂μ = polyVec A r₀ R ⬝ᵥ polyVec A r₀ R' := by sorry

end ConjGrad.ErrorDecrease.Supplement
