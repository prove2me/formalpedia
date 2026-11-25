-- Prove2me | Theorems.Thm_Arxiv1810_02867_slowness_domain_operator
-- name    : Arxiv1810_02867.slowness_domain_operator
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T05:24:28.148625+00:00
-- url     : https://prove2.me/theorems/4ba48305-898f-5fe6-819a-ec2b8769a0ed
-- title:
--   Eqs. (B21)-(B22): the operator matrix in the slowness domain
-- statement:
--   Let the medium be laterally invariant at the depth level considered, with constant real parameters $\alpha,\beta_{rs},\gamma_r$, $\beta$ symmetric, $\beta_{11}\neq0$ and $\det\beta\neq0$. Let $\omega\neq0$ and $s_1\in\mathbb R$. On plane waves $P=c_1e^{i\omega s_1x_1}$, $Q_3=c_2e^{i\omega s_1x_1}$, the operator matrix $\mathcal A$ of (B5), (B14)-(B17) acts as multiplication by
--   $$\tilde{\mathcal A}(s_1,x_3,\omega)=\begin{pmatrix}i\omega\{\gamma_3-d(s_1-\gamma_1)\}&i\omega\vartheta_{33}^{-1}\\ i\omega\vartheta_{33}s_3^2&i\omega\{\gamma_3-d(s_1-\gamma_1)\}\end{pmatrix},\qquad s_3^2=\vartheta_{33}^{-1}\big(\alpha-b_1(s_1-\gamma_1)^2\big)$$
--   (B21)-(B22). That is, $\mathcal A\big(\mathbf c\,e^{i\omega s_1x_1}\big)=e^{i\omega s_1x_1}\tilde{\mathcal A}\mathbf c$.
--
--   **Formalization Note** The paper's "the spatial differential operators $\partial_1$ are replaced by $i\omega s_1$" under the transform (45) is stated as the action of $\mathcal A$ on the plane waves $e^{i\omega s_1x_1}$, which is what that replacement means for constant coefficients.
-- source:
--   Wapenaar and Reinicke, Unified wave field retrieval and imaging method for inhomogeneous non-reciprocal media, arXiv:1810.02867v2 (2020), claim c030; Appendix B.2, eqs. (B21)-(B22), with eq. (45), PDF p. 31

import Mathlib
import Definitions.Def_Arxiv1810_02867_Basic

open MeasureTheory Matrix

namespace Arxiv1810_02867

theorem slowness_domain_operator (ω : ℝ) (hω : ω ≠ 0) (alpha : ℝ) (beta : Fin 2 → Fin 2 → ℝ)
    (gamma : Fin 2 → ℝ) (hsym : beta 0 1 = beta 1 0) (hb11 : beta 0 0 ≠ 0)
    (hdet : (Matrix.of beta).det ≠ 0) (s1 : ℝ) (c : Fin 2 → ℂ) (x1 : ℝ) :
    opA ω (fun _ => alpha) (fun _ => beta) (fun _ => gamma)
        (fun y => c 0 * Complex.exp (Complex.I * ω * s1 * y))
        (fun y => c 1 * Complex.exp (Complex.I * ω * s1 * y)) x1 =
      Complex.exp (Complex.I * ω * s1 * x1) • (Atilde ω alpha beta gamma s1).mulVec c := by sorry

end Arxiv1810_02867
