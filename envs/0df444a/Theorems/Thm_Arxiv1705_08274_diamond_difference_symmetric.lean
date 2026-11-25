-- Prove2me | Theorems.Thm_Arxiv1705_08274_diamond_difference_symmetric
-- name    : Arxiv1705_08274.diamond_difference_symmetric
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T03:24:01.686371+00:00
-- url     : https://prove2.me/theorems/9947a4f5-cad0-4b47-b792-0704bbbe6fb3
-- title:
--   Eqs. (41)-(45c): the diamond difference response matrix is symmetric
-- statement:
--   Let $A=\begin{bmatrix}\alpha&-\beta\\\beta&-\alpha\end{bmatrix}$ be the Jacobian (5c) and $h>0$. The trapezoidal (diamond difference) rule gives $Y_{j+1}=P^{*-1}PY_j$ with $P^*=I+\frac h2A$ and $P=I-\frac h2A$ (41a-c). Then:
--
--   1. $P^*_{11}=I+\frac h2\alpha$, $P^*_{12}=-\frac h2\beta$, $P^*_{21}=\frac h2\beta$, $P^*_{22}=I-\frac h2\alpha$ (44a-d);
--   2. $P^*=D_1(h)$ and $P=N_1(h)$: the scheme is the $(1,1)$ Padé approximant of $e^{-Ah}$;
--   3. $P(h)=P^*(-h)$ (45a) and $P=\begin{bmatrix}P^*_{22}&P^*_{21}\\P^*_{12}&P^*_{11}\end{bmatrix}$ (45b);
--   4. the response matrix (43) equals $\begin{bmatrix}-P^*_{21}&P^*_{11}\\-P^*_{11}&P^*_{21}\end{bmatrix}^{-1}\begin{bmatrix}-P^*_{12}&P^*_{22}\\-P^*_{22}&P^*_{12}\end{bmatrix}$ (45c);
--   5. if $P^*_{11}\mp P^*_{21}$ are invertible, the response matrix is symmetric: diamond difference preserves scattering symmetry.
--
--   **Formalization Note** The paper writes $\eta_{21}^{(1)}$ and $\eta_{22}^{(1)}$ in (44c,d). These are not defined; by (18a) the blocks are $\eta_{12}^{(1)}=\beta$ and $-\eta_{11}^{(1)}=-\alpha$, and the statement uses them. The efficiency comparison with the other schemes is numerical and is not stated.
-- source:
--   B. D. Ganapol, A 1D Radiative Transfer Benchmark with Polarization via Doubling and Adding, arXiv:1705.08274v1 (2017), claim c009; Section II.A.1, eqs. (40), (41a-c), (42a-d), (43), (44a-d), (45a-c), PDF pp. 19-21

import Mathlib
import Definitions.Def_Arxiv1705_08274_Basic

open Matrix

namespace Arxiv1705_08274

theorem diamond_difference_symmetric {N : ℕ} (S : DOModel N) (hS : S.Admissible)
    (h : ℝ) (hh : 0 < h) :
    let Ps := 1 + (h / 2) • S.jacobian
    let P := 1 - (h / 2) • S.jacobian
    (Ps.toBlocks₁₁ = 1 + (h / 2) • S.alpha ∧ Ps.toBlocks₁₂ = -((h / 2) • S.beta) ∧
      Ps.toBlocks₂₁ = (h / 2) • S.beta ∧ Ps.toBlocks₂₂ = 1 - (h / 2) • S.alpha) ∧
    (Ps = padeDen S.jacobian h 1 ∧ P = padeNum S.jacobian h 1) ∧
    P = 1 + (-h / 2) • S.jacobian ∧
    P = fromBlocks Ps.toBlocks₂₂ Ps.toBlocks₂₁ Ps.toBlocks₁₂ Ps.toBlocks₁₁ ∧
    respOfPair Ps P =
      (fromBlocks (-Ps.toBlocks₂₁) Ps.toBlocks₁₁ (-Ps.toBlocks₁₁) Ps.toBlocks₂₁)⁻¹ *
        fromBlocks (-Ps.toBlocks₁₂) Ps.toBlocks₂₂ (-Ps.toBlocks₂₂) Ps.toBlocks₁₂ ∧
    (IsUnit (Ps.toBlocks₁₁ - Ps.toBlocks₂₁).det → IsUnit (Ps.toBlocks₁₁ + Ps.toBlocks₂₁).det →
      IsSymmetricResponse (respOfPair Ps P)) := by sorry

end Arxiv1705_08274
