-- Prove2me | Theorems.Thm_ConjGrad_ErrorDecrease_Supplement_theorem_4_5
-- name    : ConjGrad.ErrorDecrease.Supplement.theorem_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-24T01:54:26.501476+00:00
-- url     : https://prove2.me/theorems/0a26c8ec-7c93-44c7-adce-952be84f89fe
-- title:
--   Theorem 4:5 — $A^{-1}$ from $n$ mutually conjugate nonzero vectors
-- statement:
--   Let $A$ be a real symmetric positive definite $n\times n$ matrix and let $p_0,\dots,p_{n-1}$ be $n$ mutually conjugate ($(p_i,Ap_j)=0$ for $i\ne j$) nonzero vectors, with $p_{ij}$ the $j$-th component of $p_i$. Then the entry of $A^{-1}$ in row $j$ and column $k$ is
--
--   $$(A^{-1})_{jk}=\sum_{i=0}^{n-1}\frac{p_{ij}\,p_{ik}}{(p_i,Ap_i)} .$$
--
--   Any cd-method therefore yields the inverse matrix as a by-product of a full set of conjugate directions.
--
--   **Formalization Note** The vectors are indexed by `Fin n` and the columns of the formula by `j l : Fin n`; `A⁻¹` is Mathlib's matrix inverse.
--
--   Differences from the source: none.
-- source:
--   Hestenes & Stiefel, Methods of Conjugate Gradients for Solving Linear Systems, J. Res. Natl. Bur. Stand. 49(6) (1952), DOI 10.6028/jres.049.044, p. 414, Theorem 4:5 (PDF p. 6)

import Mathlib

open Matrix

namespace ConjGrad.ErrorDecrease.Supplement

/-- Theorem 4:5 (Hestenes–Stiefel 1952, p. 414): from `n` mutually conjugate nonzero vectors,
`(A⁻¹)ⱼₗ = ∑ᵢ pᵢⱼ pᵢₗ / (pᵢ, Apᵢ)`. -/
theorem theorem_4_5 {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (hA : A.PosDef)
    (p : Fin n → Fin n → ℝ) (hp : ∀ i, p i ≠ 0)
    (hconj : ∀ i j, i ≠ j → p i ⬝ᵥ (A *ᵥ p j) = 0) (j l : Fin n) :
    A⁻¹ j l = ∑ i, p i j * p i l / (p i ⬝ᵥ (A *ᵥ p i)) := by sorry

end ConjGrad.ErrorDecrease.Supplement
