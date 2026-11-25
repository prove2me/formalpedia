-- Prove2me | Theorems.Thm_Arxiv1810_02867_composition_operator_symmetries
-- name    : Arxiv1810_02867.composition_operator_symmetries
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T05:25:42.903321+00:00
-- url     : https://prove2.me/theorems/f3ed4a5f-d075-41a8-a845-49323a223bb9
-- title:
--   Eqs. (B37)-(B38): symmetry properties of the composition operator
-- statement:
--   Let $\alpha>0$, let $\beta$ be symmetric positive definite, and let $\gamma_1,\gamma_3\in\mathbb R$. Write $\tilde{\mathcal L}^{(c)}$ for $\tilde{\mathcal L}$ of (B25) computed with $\gamma_r$ replaced by $-\gamma_r$. Let
--   $$\mathbf N=\begin{pmatrix}0&1\\-1&0\end{pmatrix},\quad\mathbf K=\begin{pmatrix}0&1\\1&0\end{pmatrix},\quad\mathbf J=\begin{pmatrix}1&0\\0&-1\end{pmatrix}.$$
--   Then:
--
--   1. (B37) for every real $s_1$ with $(s_1-\gamma_1)^2\neq\alpha/b_1$ (propagating and evanescent waves),
--   $$\{\tilde{\mathcal L}^{(c)}(-s_1)\}^t\,\mathbf N\,\tilde{\mathcal L}(s_1)=-\mathbf N;$$
--   2. (B38) for every real $s_1$ with $(s_1-\gamma_1)^2<\alpha/b_1$ (propagating waves),
--   $$\{\tilde{\mathcal L}(s_1)\}^\dagger\,\mathbf K\,\tilde{\mathcal L}(s_1)=\mathbf J.$$
--
--   **Formalization Note** The paper states (B37) for all $-\infty<s_1<\infty$ and (B38) for $(s_1-\gamma_1)^2\le\alpha/b_1$. At the two points $(s_1-\gamma_1)^2=\alpha/b_1$ one has $s_3=0$, and $\tilde{\mathcal L}$ contains $1/\sqrt0$, so these points are excluded. Positivity of $\alpha$ and $\beta$ is assumed as in (B23)-(B28).
-- source:
--   Wapenaar and Reinicke, Unified wave field retrieval and imaging method for inhomogeneous non-reciprocal media, arXiv:1810.02867v2 (2020), claim c032; Appendix B.3, eqs. (B31), (B37)-(B39), PDF pp. 32-33

import Mathlib
import Definitions.Def_Arxiv1810_02867_Basic

open MeasureTheory Matrix

namespace Arxiv1810_02867

theorem composition_operator_symmetries (alpha : ℝ) (beta : Fin 2 → Fin 2 → ℝ)
    (gamma : Fin 2 → ℝ) (halpha : 0 < alpha) (hsym : beta 0 1 = beta 1 0) (hb11 : 0 < beta 0 0)
    (hdet : 0 < (Matrix.of beta).det) :
    (∀ s1 : ℝ, (s1 - gamma 0) ^ 2 ≠ alpha / bCoef beta 0 →
      (Ltilde alpha beta (-gamma) (-s1))ᵀ * Nmat * Ltilde alpha beta gamma s1 = -Nmat) ∧
    (∀ s1 : ℝ, (s1 - gamma 0) ^ 2 < alpha / bCoef beta 0 →
      (Ltilde alpha beta gamma s1)ᴴ * Kmat * Ltilde alpha beta gamma s1 = Jmat) := by sorry

end Arxiv1810_02867
