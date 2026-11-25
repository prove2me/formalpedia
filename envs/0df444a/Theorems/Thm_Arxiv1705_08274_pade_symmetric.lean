-- Prove2me | Theorems.Thm_Arxiv1705_08274_pade_symmetric
-- name    : Arxiv1705_08274.pade_symmetric
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T03:27:26.58084+00:00
-- url     : https://prove2.me/theorems/2ece7de4-dc8f-4b2a-a86c-c99c394a5116
-- title:
--   Eqs. (46a)-(49): the $(q,q)$ Padé response matrix is symmetric
-- statement:
--   Let $A$ be the Jacobian (5c), $h>0$ and $q\ge1$. Let $N_q$ and $D_q$ be the $(q,q)$ Padé polynomials (46b,c); the paper uses $D_q(h)^{-1}N_q(h)$ as an approximation of $e^{-Ah}$, but that approximation is not part of this statement. Set $P^*_q(h)=D_q(h)$ and $P_q(h)=N_q(h)$ (48a,b). Then
--
--   $$P_q(h)=D_q(-h)=P^*_q(-h)=\begin{bmatrix}P^*_{q,22}&P^*_{q,21}\\P^*_{q,12}&P^*_{q,11}\end{bmatrix},$$
--
--   and the response matrix of the scheme has the form (49):
--
--   $$R=\begin{bmatrix}-P^*_{q,21}&P^*_{q,11}\\-P^*_{q,11}&P^*_{q,21}\end{bmatrix}^{-1}\begin{bmatrix}-P^*_{q,12}&P^*_{q,22}\\-P^*_{q,22}&P^*_{q,12}\end{bmatrix}.$$
--
--   If $P^*_{q,11}\mp P^*_{q,21}$ are invertible, $R$ is symmetric.
--
--   **Formalization Note** The Padé coefficients are $\frac{(2q-j)!\,q!}{(2q)!\,j!\,(q-j)!}$ (Moler and Van Loan). The paper prints $(q-j)$ in place of $(q-j)!$, which is zero for $j=q$. The approximation $D_q(h)^{-1}N_q(h)\simeq e^{-Ah}$ and the remark that the $(1,1)$ approximant is the most efficient are not stated.
-- source:
--   B. D. Ganapol, A 1D Radiative Transfer Benchmark with Polarization via Doubling and Adding, arXiv:1705.08274v1 (2017), claim c010; Section II.A.2, eqs. (46a), (46b,c), (47), (48a,b), (49), PDF pp. 22-23

import Mathlib
import Definitions.Def_Arxiv1705_08274_Basic

open Matrix

namespace Arxiv1705_08274

theorem pade_symmetric {N : ℕ} (S : DOModel N) (hS : S.Admissible)
    (h : ℝ) (hh : 0 < h) (q : ℕ) (hq : 1 ≤ q) :
    let Ps := padeDen S.jacobian h q
    let P := padeNum S.jacobian h q
    P = padeDen S.jacobian (-h) q ∧
    P = fromBlocks Ps.toBlocks₂₂ Ps.toBlocks₂₁ Ps.toBlocks₁₂ Ps.toBlocks₁₁ ∧
    respOfPair Ps P =
      (fromBlocks (-Ps.toBlocks₂₁) Ps.toBlocks₁₁ (-Ps.toBlocks₁₁) Ps.toBlocks₂₁)⁻¹ *
        fromBlocks (-Ps.toBlocks₁₂) Ps.toBlocks₂₂ (-Ps.toBlocks₂₂) Ps.toBlocks₁₂ ∧
    (IsUnit (Ps.toBlocks₁₁ - Ps.toBlocks₂₁).det → IsUnit (Ps.toBlocks₁₁ + Ps.toBlocks₂₁).det →
      IsSymmetricResponse (respOfPair Ps P)) := by sorry

end Arxiv1705_08274
