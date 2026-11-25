-- Prove2me | Theorems.Thm_Arxiv1705_08274_jacobian_power_block_structure
-- name    : Arxiv1705_08274.jacobian_power_block_structure
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T02:07:10.632336+00:00
-- url     : https://prove2.me/theorems/a16753e0-ad9d-4a09-97b7-2eb3f33dd884
-- title:
--   Eqs. (18a)-(18c): block structure of the powers of the Jacobian
-- statement:
--   Let $A=\begin{bmatrix}\alpha&-\beta\\\beta&-\alpha\end{bmatrix}$ be the Jacobian (5c) of the discrete ordinates equations, with $\alpha=M^{-1}(I-PW)$ and $\beta=M^{-1}PW$. This holds for any admissible quadrature set, albedo and scattering matrix factor. Then
--
--   $$A^2=\begin{bmatrix}\alpha^2-\beta^2&-\alpha\beta+\beta\alpha\\\beta\alpha-\alpha\beta&-\beta^2+\alpha^2\end{bmatrix},$$
--
--   and for every integer $m\ge1$ there are matrices $\gamma_{11}^{(m)},\gamma_{12}^{(m)},\eta_{11}^{(m)},\eta_{12}^{(m)}$ of order $2N$ with
--
--   $$A^{2m}=\begin{bmatrix}\gamma_{11}^{(m)}&\gamma_{12}^{(m)}\\\gamma_{12}^{(m)}&\gamma_{11}^{(m)}\end{bmatrix},\qquad A^{2m-1}=\begin{bmatrix}\eta_{11}^{(m)}&-\eta_{12}^{(m)}\\\eta_{12}^{(m)}&-\eta_{11}^{(m)}\end{bmatrix}.$$
--
--   Even powers have equal diagonal and equal off-diagonal blocks (the paper's "symmetry"). Odd powers keep the sign pattern of $A$.
--
--   **Formalization Note** The paper's word "symmetric" means this block pattern, not transpose symmetry. The off-diagonal blocks of $A^2$ are written as in (18b); Appendix A's (A2) prints them as $-\alpha\beta+\alpha\beta$ and $\alpha\beta-\alpha\beta$, a misprint.
-- source:
--   B. D. Ganapol, A 1D Radiative Transfer Benchmark with Polarization via Doubling and Adding, arXiv:1705.08274v1 (2017), claim c001; Section I.C.2, eqs. (18a), (18b), (18c) and the unnumbered odd-power equation, PDF pp. 9-10; proof in Appendix A, eqs. (A1)-(A5), PDF pp. 39-40

import Mathlib
import Definitions.Def_Arxiv1705_08274_Basic

open Matrix

namespace Arxiv1705_08274

theorem jacobian_power_block_structure {N : ℕ} (S : DOModel N) (hS : S.Admissible)
    (m : ℕ) (hm : 1 ≤ m) :
    S.jacobian ^ 2 = fromBlocks (S.alpha * S.alpha - S.beta * S.beta)
      (-(S.alpha * S.beta) + S.beta * S.alpha) (S.beta * S.alpha - S.alpha * S.beta)
      (-(S.beta * S.beta) + S.alpha * S.alpha) ∧
    (∃ γ₁₁ γ₁₂ : Matrix (Dir N) (Dir N) ℝ,
      S.jacobian ^ (2 * m) = fromBlocks γ₁₁ γ₁₂ γ₁₂ γ₁₁) ∧
    (∃ η₁₁ η₁₂ : Matrix (Dir N) (Dir N) ℝ,
      S.jacobian ^ (2 * m - 1) = fromBlocks η₁₁ (-η₁₂) η₁₂ (-η₁₁)) := by sorry

end Arxiv1705_08274
