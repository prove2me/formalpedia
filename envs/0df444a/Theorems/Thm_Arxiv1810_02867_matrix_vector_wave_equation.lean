-- Prove2me | Theorems.Thm_Arxiv1810_02867_matrix_vector_wave_equation
-- name    : Arxiv1810_02867.matrix_vector_wave_equation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T05:24:05.918207+00:00
-- url     : https://prove2.me/theorems/12d477c2-d0d7-4727-965c-f5174f37ac13
-- title:
--   Eqs. (B3)-(B20): unified matrix-vector wave equation
-- statement:
--   Let $\omega\neq0$. Let the real parameters $\alpha,\beta_{rs},\gamma_r$ on the plane have $\beta$ symmetric, $\beta_{11}\neq0$ and $\det\beta\neq0$ everywhere, with $\beta,\gamma$ of class $C^1$. Let $P$ be $C^2$, $Q_r$ be $C^1$, and $C_r$ be $C^1$, and suppose eqs. (B1)-(B2)
--   $$-i\omega\alpha P+(\partial_r-i\omega\gamma_r)Q_r=B,\qquad (\partial_s-i\omega\gamma_s)P-i\omega\beta_{su}Q_u=C_s$$
--   hold everywhere. Then:
--
--   1. $b_1=1/\beta_{11}$, $b_3=0$ and $d=-\beta_{31}/\beta_{11}$ (B12), (B13), (B20);
--   2. $\mathbf q=(P,Q_3)$ satisfies the matrix-vector wave equation (B3)
--   $$\partial_3\mathbf q=\mathcal A\mathbf q+\mathbf d,$$
--   with $\mathcal A_{11}=i\omega\gamma_3-d(\partial_1-i\omega\gamma_1)$, $\mathcal A_{12}=i\omega\vartheta_{33}^{-1}$, $\mathcal A_{21}=i\omega\alpha-\frac1{i\omega}(\partial_1-i\omega\gamma_1)b_1(\partial_1-i\omega\gamma_1)$, $\mathcal A_{22}=i\omega\gamma_3-(\partial_1-i\omega\gamma_1)d$ (B14)-(B17). The source vector is $\mathbf d=(C^o,B^o)$ with $C^o=dC_1+C_3$ and $B^o=B+\frac1{i\omega}(\partial_1-i\omega\gamma_1)b_1C_1$ (B18)-(B19). Here $d=\vartheta_{33}^{-1}\vartheta_{13}$, $b_s=\vartheta_{1s}-\vartheta_{13}\vartheta_{33}^{-1}\vartheta_{3s}$, and differential operators act on all factors to their right.
--
--   **Formalization Note** The operators involve only $\partial_1$. They are applied at each depth $x_3$ to the restrictions of the fields and parameters to that depth level.
-- source:
--   Wapenaar and Reinicke, Unified wave field retrieval and imaging method for inhomogeneous non-reciprocal media, arXiv:1810.02867v2 (2020), claim c029; Appendix B.1, eqs. (B1)-(B20), PDF pp. 29-30

import Mathlib
import Definitions.Def_Arxiv1810_02867_Basic

open MeasureTheory Matrix

namespace Arxiv1810_02867

theorem matrix_vector_wave_equation (ω : ℝ) (hω : ω ≠ 0) (S : FreqState)
    (h : FreqEqs ω S Set.univ) (hsym : ∀ x r s, S.beta x r s = S.beta x s r)
    (hb11 : ∀ x, S.beta x 0 0 ≠ 0) (hdet : ∀ x, (Matrix.of (S.beta x)).det ≠ 0)
    (hP : ContDiff ℝ 2 S.P) (hQ : ContDiff ℝ 1 S.Q) (hbeta : ContDiff ℝ 1 S.beta)
    (hgamma : ContDiff ℝ 1 S.gamma) (hC : ContDiff ℝ 1 S.C) :
    (∀ x, bCoef (S.beta x) 0 = 1 / S.beta x 0 0 ∧ bCoef (S.beta x) 1 = 0 ∧
      dCoef (S.beta x) = -S.beta x 1 0 / S.beta x 0 0) ∧
    ∀ x1 x3 : ℝ,
      ![pd 1 S.P (pt x1 x3), pd 1 (fun y => S.Q y 1) (pt x1 x3)] =
        opA ω (fun y => S.alpha (pt y x3)) (fun y => S.beta (pt y x3))
            (fun y => S.gamma (pt y x3)) (fun y => S.P (pt y x3)) (fun y => S.Q (pt y x3) 1) x1 +
          srcVec ω (fun y => S.beta (pt y x3)) (fun y => S.gamma (pt y x3))
            (fun y => S.B (pt y x3)) (fun y => S.C (pt y x3)) x1 := by sorry

end Arxiv1810_02867
