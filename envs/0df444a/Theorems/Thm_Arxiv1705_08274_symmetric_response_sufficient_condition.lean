-- Prove2me | Theorems.Thm_Arxiv1705_08274_symmetric_response_sufficient_condition
-- name    : Arxiv1705_08274.symmetric_response_sufficient_condition
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T03:20:57.428999+00:00
-- url     : https://prove2.me/theorems/92a45251-728a-412c-9948-ab0b540cab54
-- title:
--   Appendix B, eqs. (B1)-(B9): a sufficient condition for a symmetric response matrix
-- statement:
--   Let $P^*=\begin{bmatrix}P^*_{11}&P^*_{12}\\P^*_{21}&P^*_{22}\end{bmatrix}$ (blocks of order $2N$) and suppose
--
--   $$P=\begin{bmatrix}P^*_{22}&P^*_{21}\\P^*_{12}&P^*_{11}\end{bmatrix}\quad(B2b).$$
--
--   Assume $P^*_{11}-P^*_{21}$ and $P^*_{11}+P^*_{21}$ are invertible. Let $R=\begin{bmatrix}-P_{12}&P^*_{11}\\-P_{22}&P^*_{21}\end{bmatrix}^{-1}\begin{bmatrix}-P^*_{12}&P_{11}\\-P^*_{22}&P_{21}\end{bmatrix}$ be the response matrix (B1) of the scheme $Y_{j+1}=P^{*-1}PY_j$. Then:
--
--   1. $R=\begin{bmatrix}-P^*_{21}&P^*_{11}\\-P^*_{11}&P^*_{21}\end{bmatrix}^{-1}\begin{bmatrix}-P^*_{12}&P^*_{22}\\-P^*_{22}&P^*_{12}\end{bmatrix}$ (B3);
--   2. $\begin{bmatrix}P^*_{11}&-P^*_{21}\\-P^*_{21}&P^*_{11}\end{bmatrix}^{-1}=\begin{bmatrix}T_1^*&T_2^*\\T_2^*&T_1^*\end{bmatrix}$ with $T^*_{1,2}=\tfrac12\big[(P^*_{11}-P^*_{21})^{-1}\pm(P^*_{11}+P^*_{21})^{-1}\big]$ (B5)-(B7);
--   3. $R=\begin{bmatrix}T_1^*&T_2^*\\T_2^*&T_1^*\end{bmatrix}\begin{bmatrix}P^*_{22}&-P^*_{12}\\-P^*_{12}&P^*_{22}\end{bmatrix}$ (B8);
--   4. $R=\begin{bmatrix}T_n&R_f\\R_f&T_n\end{bmatrix}$ is symmetric, with
--   $$\begin{matrix}T_n\\R_f\end{matrix}=\tfrac12\Big[(P^*_{11}-P^*_{21})^{-1}(P^*_{22}-P^*_{12})\pm(P^*_{11}+P^*_{21})^{-1}(P^*_{22}+P^*_{12})\Big]\quad(B9).$$
--
--   This is the sufficient condition used for the diamond difference, Padé and RK5 node approximations.
--
--   **Formalization Note** The two invertibility hypotheses are not stated in the paper. Under (B2b) they are equivalent to the invertibility of the matrix inverted in (B1).
-- source:
--   B. D. Ganapol, A 1D Radiative Transfer Benchmark with Polarization via Doubling and Adding, arXiv:1705.08274v1 (2017), claim c008; Section II.A.1, PDF p. 21; Appendix B, eqs. (B1), (B2b), (B3)-(B9), PDF pp. 40-42

import Mathlib
import Definitions.Def_Arxiv1705_08274_Basic

open Matrix

namespace Arxiv1705_08274

theorem symmetric_response_sufficient_condition {N : ℕ}
    (Ps P : Matrix (Dir N ⊕ Dir N) (Dir N ⊕ Dir N) ℝ)
    (hP : P = fromBlocks Ps.toBlocks₂₂ Ps.toBlocks₂₁ Ps.toBlocks₁₂ Ps.toBlocks₁₁)
    (hm : IsUnit (Ps.toBlocks₁₁ - Ps.toBlocks₂₁).det)
    (hp : IsUnit (Ps.toBlocks₁₁ + Ps.toBlocks₂₁).det) :
    let P11 := Ps.toBlocks₁₁
    let P12 := Ps.toBlocks₁₂
    let P21 := Ps.toBlocks₂₁
    let P22 := Ps.toBlocks₂₂
    let T1 := (1 / 2 : ℝ) • ((P11 - P21)⁻¹ + (P11 + P21)⁻¹)
    let T2 := (1 / 2 : ℝ) • ((P11 - P21)⁻¹ - (P11 + P21)⁻¹)
    let Tn := (1 / 2 : ℝ) • ((P11 - P21)⁻¹ * (P22 - P12) + (P11 + P21)⁻¹ * (P22 + P12))
    let Rf := (1 / 2 : ℝ) • ((P11 - P21)⁻¹ * (P22 - P12) - (P11 + P21)⁻¹ * (P22 + P12))
    respOfPair Ps P = (fromBlocks (-P21) P11 (-P11) P21)⁻¹ * fromBlocks (-P12) P22 (-P22) P12 ∧
    (fromBlocks P11 (-P21) (-P21) P11)⁻¹ = fromBlocks T1 T2 T2 T1 ∧
    respOfPair Ps P = fromBlocks T1 T2 T2 T1 * fromBlocks P22 (-P12) (-P12) P22 ∧
    respOfPair Ps P = fromBlocks Tn Rf Rf Tn := by sorry

end Arxiv1705_08274
