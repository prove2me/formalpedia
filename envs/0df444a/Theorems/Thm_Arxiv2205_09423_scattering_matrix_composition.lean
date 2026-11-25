-- Prove2me | Theorems.Thm_Arxiv2205_09423_scattering_matrix_composition
-- name    : Arxiv2205_09423.scattering_matrix_composition
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T12:37:23.860059+00:00
-- url     : https://prove2.me/theorems/47f7be3d-6041-5cd4-99eb-83e63ae12883
-- title:
--   Eqs. (B1)–(B2): composition law for the scattering matrices of two reciprocal slabs
-- statement:
--   Let $\mathbf S_1=\begin{pmatrix}\mathbf r_1&\mathbf t_1'\\\mathbf t_1&\mathbf r_1'\end{pmatrix}$ and $\mathbf S_2=\begin{pmatrix}\mathbf r_2&\mathbf t_2'\\\mathbf t_2&\mathbf r_2'\end{pmatrix}$ be the normalized scattering matrices, of size $2\cdot2(2N_k+1)$, of two reciprocal slabs, $\mathcal S_1$ to the left of $\mathcal S_2$. Reciprocal means $\mathbf S_m=\Pi\mathbf S_m^{\mathrm T}\Pi$ with $\Pi=\mathrm{diag}(\mathbf J_{2N_k+1}\otimes\boldsymbol\sigma_z,\mathbf J_{2N_k+1}\otimes\boldsymbol\sigma_z)$. Suppose $\mathbb I-\mathbf r_1'\mathbf r_2$ is invertible and put $\mathbf Q=(\mathbb I-\mathbf r_1'\mathbf r_2)^{-1}$. Then a matrix $\mathbf S$ is the scattering matrix of the combined system if and only if
--
--   $$\mathbf S=\begin{pmatrix}\mathbf r_1+\mathbf t_1'\mathbf r_2\mathbf Q\mathbf t_1&(\mathbf J_{2N_k+1}\otimes\boldsymbol\sigma_z)(\mathbf t_2\mathbf Q\mathbf t_1)^{\mathrm T}(\mathbf J_{2N_k+1}\otimes\boldsymbol\sigma_z)\\\mathbf t_2\mathbf Q\mathbf t_1&\mathbf r_2'+\mathbf t_2\mathbf Q\mathbf r_1'\mathbf t_2'\end{pmatrix}.$$
--
--   Here $\mathbf J_n$ is the exchange matrix and $\boldsymbol\sigma_z=\mathrm{diag}(1,-1)$. This composition law cascades scattering matrices directly, as an alternative to multiplying transfer matrices.
--
--   **Formalization Note** "Scattering matrix of the combined system" is defined by the matching conditions between the slabs (see the definitions). The upper-right block is written through reciprocity, so the formula is stated for reciprocal slabs. The reciprocity relation is that of Byrnes and Foreman (2021), Eq. (98), which this paper uses. For non-reciprocal slabs that block is $\mathbf t_1'(\mathbb I-\mathbf r_2\mathbf r_1')^{-1}\mathbf t_2'$.
-- source:
--   Byrnes and Foreman, Random matrix theory of polarized light scattering in disordered media, arXiv:2205.09423v1 (2022), claim c024; Appendix B, Eqs. (B1)-(B2), PDF pp. 24-25

import Mathlib
import Definitions.Def_Arxiv2205_09423_Basic

open MeasureTheory ProbabilityTheory Matrix

namespace Arxiv2205_09423

theorem scattering_matrix_composition {Nk : ℕ}
    (S1 S2 : Matrix (MIdx Nk ⊕ MIdx Nk) (MIdx Nk ⊕ MIdx Nk) ℂ)
    (h1 : IsReciprocal S1) (h2 : IsReciprocal S2)
    (hQ : IsUnit (1 - S1.toBlocks₂₂ * S2.toBlocks₁₁).det)
    (S : Matrix (MIdx Nk ⊕ MIdx Nk) (MIdx Nk ⊕ MIdx Nk) ℂ) :
    let r1 := S1.toBlocks₁₁
    let t1p := S1.toBlocks₁₂
    let t1 := S1.toBlocks₂₁
    let r1p := S1.toBlocks₂₂
    let r2 := S2.toBlocks₁₁
    let t2p := S2.toBlocks₁₂
    let t2 := S2.toBlocks₂₁
    let r2p := S2.toBlocks₂₂
    let Q := (1 - r1p * r2)⁻¹
    IsCascade S1 S2 S ↔
      S = Matrix.fromBlocks (r1 + t1p * r2 * Q * t1)
        (piMat Nk * (t2 * Q * t1).transpose * piMat Nk) (t2 * Q * t1) (r2p + t2 * Q * r1p * t2p) := by sorry

end Arxiv2205_09423
