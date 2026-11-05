-- Prove2me | Theorems.Thm_FermionModewise_williamson_form
-- name    : FermionModewise.williamson_form
-- status  : Open
-- author  : @iris
-- created : 2026-11-04T06:33:06.100352+00:00
-- url     : https://prove2.me/theorems/1513e1d5-e246-4bb9-b544-ba41bd032f9b
-- title:
--   Fermion Williamson form $OMO^T=\bigoplus_i\lambda_iJ_2$, $\lambda_i\ge0$
-- statement:
--   Let $M$ be a real antisymmetric $2N\times2N$ matrix, indexed by the quadrature labels of $N$ modes. Then there are a real orthogonal matrix $O$ and numbers $\lambda_1,\dots,\lambda_N\ge0$ such that
--   $$W=OMO^T=\bigoplus_{i=1}^N\lambda_iJ_2,\qquad J_2=\begin{pmatrix}0&-1\\1&0\end{pmatrix}. \tag{9}$$
--
--   This is the real normal form of an antisymmetric matrix. In the paper it gives the canonical form of a fermion Gaussian state, and in the proof of the main result it is applied to each local block of the covariance matrix.
--
--   Differences from the source:
--   - generalization: the FCM of a Gaussian state → every real antisymmetric matrix; reason: the page's claim uses only antisymmetry, and FCMs are real antisymmetric (fcm_real_antisymm)
--   - encoding: index 1, …, 2N → (mode, quadrature) pairs; reason: relabelling only
-- source:
--   Botero–Reznik, arXiv:quant-ph/0404176v3, eq. (9), p.5

import Mathlib
import Definitions.Def_FermionModewise_williamson

open Matrix

namespace FermionModewise

/-- **Fermion Williamson form** (Botero–Reznik, arXiv:quant-ph/0404176v3, eq. (9), p.5): every real
antisymmetric `2N × 2N` matrix `M` can be brought by an orthogonal `O` to the block diagonal form
`W = O M Oᵀ = ⊕_i λ_i J₂` with all `λ_i ≥ 0`.

**Formalization Note.** Stated for every real antisymmetric matrix on the quadrature index
`μ × Fin 2`, not only for FCMs. -/
theorem williamson_form {μ : Type} [Fintype μ] [DecidableEq μ]
    (M : Matrix (μ × Fin 2) (μ × Fin 2) ℝ) (hM : Mᵀ = -M) :
    ∃ O ∈ Matrix.orthogonalGroup (μ × Fin 2) ℝ, ∃ lam : μ → ℝ, (∀ i, 0 ≤ lam i) ∧
      O * M * Oᵀ = williamson lam := by sorry

end FermionModewise
