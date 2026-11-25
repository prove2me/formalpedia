-- Prove2me | Theorems.Thm_Arxiv1810_02867_ac_system
-- name    : Arxiv1810_02867.ac_system
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T05:19:11.281799+00:00
-- url     : https://prove2.me/theorems/baf1ffe7-6f39-49a3-a99d-1cdca22b8162
-- title:
--   Eqs. (A68)-(A70): acoustic waves in the $(x_1,x_3)$-plane
-- statement:
--   Let $v,p,F,q$ and the parameters $\rho^o,\xi,\kappa$ be independent of $x_2$ and satisfy (A66)-(A67). Let $\rho^o$ be symmetric, with $\rho^o_{12}=\rho^o_{32}=0$ and $\xi_2=0$. Then, in the $(x_1,x_3)$-plane, $(p,v_1,v_3)$ satisfy the acoustic system (A68)-(A70):
--   $$\kappa\partial_tp+\xi_1\partial_tv_1+\xi_3\partial_tv_3+\partial_1v_1+\partial_3v_3=q,$$
--   $$\rho^o_{11}\partial_tv_1+\rho^o_{31}\partial_tv_3+\xi_1\partial_tp+\partial_1p=F_1,\qquad \rho^o_{31}\partial_tv_1+\rho^o_{33}\partial_tv_3+\xi_3\partial_tp+\partial_3p=F_3.$$
--
--   **Formalization Note** The $x_2$-independent quantities are restricted to the plane $x_2=0$.
-- source:
--   Wapenaar and Reinicke, Unified wave field retrieval and imaging method for inhomogeneous non-reciprocal media, arXiv:1810.02867v2 (2020), claim c027; Appendix A.3, eqs. (A66)-(A70), PDF pp. 27-28

import Mathlib
import Definitions.Def_Arxiv1810_02867_Basic

open MeasureTheory Matrix

namespace Arxiv1810_02867

theorem ac_system (rhoO : Space → Fin 3 → Fin 3 → ℝ) (xi : Space → Fin 3 → ℝ)
    (kappa : Space → ℝ) (v F : Space → ℝ → Fin 3 → ℝ) (pr q : Space → ℝ → ℝ)
    (hiv : IndepX2 v) (hipr : IndepX2 pr) (hiF : IndepX2 F) (hiq : IndepX2 q)
    (hirho : IndepX2 rhoO) (hixi : IndepX2 xi) (hikappa : IndepX2 kappa)
    (hrhosym : ∀ x i j, rhoO x i j = rhoO x j i)
    (hrho0 : ∀ x, rhoO x 0 1 = 0 ∧ rhoO x 2 1 = 0) (hxi2 : ∀ x, xi x 1 = 0)
    (hA : AcousticEqs rhoO xi kappa v pr F q) :
    ACSystem (restr rhoO) (restr xi) (restr kappa) (restr v) (restr pr) (restr F) (restr q) := by sorry

end Arxiv1810_02867
