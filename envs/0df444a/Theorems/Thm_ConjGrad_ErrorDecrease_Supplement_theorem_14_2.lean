-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_Supplement_theorem_14_2
-- name    : ConjGrad.ErrorDecrease.Supplement.theorem_14_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T02:04:23.941693+00:00
-- url     : https://prove2.me/theorems/8d0dc74d-b8cd-490d-9f46-d0d54e62224e
-- title:
--   Theorem 14:2 — isometry for the weight $\lambda\,dm(\lambda)$ and the $A$-metric, (14:9)
-- statement:
--   Let $m(\lambda)$ be a mass distribution on $[0,l]$ related to an $n\times n$ matrix $A$ and a vector $r_0$ as in §14. For polynomials $R,R'$ of degree at most $n-1$ with corresponding vectors $r=R(A)r_0$, $r'=R'(A)r_0$,
--
--   $$\int_0^lR(\lambda)R'(\lambda)\,\lambda\,dm(\lambda)=(Ar,r'), \tag{14:9}$$
--
--   that is, the correspondence is isometric for the weight $\lambda\,dm(\lambda)$ on polynomials and the metric determined by $A$ on vectors.
--
--   Together with Theorem 14:1 this identifies conjugacy of vectors with orthogonality of polynomials for the weight $\lambda\,dm$, as used in §15.
--
--   **Formalization Note** The mass distribution is its Lebesgue–Stieltjes measure $\mu$ on $[0,l]$ (`IsSpectralModel μ l A r₀`); `polyVec A r₀ R` is $R(A)r_0$.
--
--   Differences from the source:
--   - generalization: $A$ positive definite with the Gauss nodes as eigenvalues; $m$ of type (a) or (b) → any matrix and mass distribution satisfying the relation `IsSpectralModel`; reason: every configuration of §14 satisfies the relation, so the statement specializes to the source's
--   - encoding: $\deg R\le n-1$ → `R.degree < n`; reason: same polynomials; avoids natural-number subtraction at $n=0$
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 429, Theorem 14:2, eq. (14:9) (PDF p. 21)

import Mathlib
import Definitions.Def_ConjGrad_ErrorDecrease_Supplement_IsSpectralModel

open Matrix MeasureTheory

namespace ConjGrad.ErrorDecrease.Supplement

/-- Theorem 14:2 (Hestenes–Stiefel 1952, p. 429), eq. (14:9): for a mass distribution related to `A`
and `r₀` as in §14, `∫₀ˡ R(λ)R'(λ) λ dm(λ) = (Ar, r')` for the vectors `r = R(A)r₀`,
`r' = R'(A)r₀` corresponding to polynomials of degree at most `n − 1`. -/
theorem theorem_14_2 {n : ℕ} (μ : Measure ℝ) (l : ℝ) (A : Matrix (Fin n) (Fin n) ℝ)
    (r₀ : Fin n → ℝ) (hrel : IsSpectralModel μ l A r₀) (R R' : Polynomial ℝ)
    (hR : R.degree < n) (hR' : R'.degree < n) :
    ∫ t, R.eval t * R'.eval t * t ∂μ = (A *ᵥ polyVec A r₀ R) ⬝ᵥ polyVec A r₀ R' := by sorry

end ConjGrad.ErrorDecrease.Supplement
