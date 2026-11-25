-- Prove2me | Theorems.Thm_Arxiv1810_02867_operator_eigendecomposition
-- name    : Arxiv1810_02867.operator_eigendecomposition
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T05:25:01.578137+00:00
-- url     : https://prove2.me/theorems/3210a8f7-e977-4827-932a-1a221a5712ec
-- title:
--   Eqs. (B23)-(B28): eigenvalue decomposition of the operator matrix
-- statement:
--   Let $\alpha>0$, let $\beta$ be symmetric positive definite ($\beta_{11}>0$, $\det\beta>0$), and let $\gamma_1,\gamma_3,\omega,s_1\in\mathbb R$ with $(s_1-\gamma_1)^2\neq\alpha/b_1$. Let $s_3$ be given by (B28): $s_3=\sqrt{\vartheta_{33}^{-1}(\alpha-b_1(s_1-\gamma_1)^2)}$ for $(s_1-\gamma_1)^2\le\alpha/b_1$ and $s_3=i\sqrt{\vartheta_{33}^{-1}(b_1(s_1-\gamma_1)^2-\alpha)}$ otherwise. Let $\lambda^\pm=s_3\pm\{\gamma_3-d(s_1-\gamma_1)\}$ (B27). Then, with
--   $$\tilde{\mathcal H}=\begin{pmatrix}i\omega\lambda^+&0\\0&-i\omega\lambda^-\end{pmatrix},\qquad\tilde{\mathcal L}=\frac1{\sqrt2}\begin{pmatrix}1/\sqrt{\vartheta_{33}s_3}&1/\sqrt{\vartheta_{33}s_3}\\ \sqrt{\vartheta_{33}s_3}&-\sqrt{\vartheta_{33}s_3}\end{pmatrix},$$
--   the inverse of $\tilde{\mathcal L}$ is
--   $$\tilde{\mathcal L}^{-1}=\frac1{\sqrt2}\begin{pmatrix}\sqrt{\vartheta_{33}s_3}&1/\sqrt{\vartheta_{33}s_3}\\ \sqrt{\vartheta_{33}s_3}&-1/\sqrt{\vartheta_{33}s_3}\end{pmatrix}$$
--   (B26), and $\tilde{\mathcal A}=\tilde{\mathcal L}\tilde{\mathcal H}\tilde{\mathcal L}^{-1}$ (B23).
--
--   **Formalization Note** At $(s_1-\gamma_1)^2=\alpha/b_1$ one has $s_3=0$, and $\tilde{\mathcal L}$ of (B25) contains $1/\sqrt0$. The paper's case $\le$ includes this point, so it is excluded here. Positivity of $\alpha$ and $\beta$ is the physical convention that makes the square roots of (B28) real where the paper takes them to be real. $\sqrt{\cdot}$ of the complex number $\vartheta_{33}s_3$ is the principal square root; any square root gives the same identities.
-- source:
--   Wapenaar and Reinicke, Unified wave field retrieval and imaging method for inhomogeneous non-reciprocal media, arXiv:1810.02867v2 (2020), claim c031; Appendix B.2, eqs. (B23)-(B28), PDF p. 31

import Mathlib
import Definitions.Def_Arxiv1810_02867_Basic

open MeasureTheory Matrix

namespace Arxiv1810_02867

theorem operator_eigendecomposition (ω alpha : ℝ) (beta : Fin 2 → Fin 2 → ℝ) (gamma : Fin 2 → ℝ)
    (s1 : ℝ) (halpha : 0 < alpha) (hsym : beta 0 1 = beta 1 0) (hb11 : 0 < beta 0 0)
    (hdet : 0 < (Matrix.of beta).det) (hs : (s1 - gamma 0) ^ 2 ≠ alpha / bCoef beta 0) :
    (Ltilde alpha beta gamma s1)⁻¹ = LtildeInv alpha beta gamma s1 ∧
    Atilde ω alpha beta gamma s1 =
      Ltilde alpha beta gamma s1 * Htilde ω alpha beta gamma s1 * (Ltilde alpha beta gamma s1)⁻¹ := by sorry

end Arxiv1810_02867
