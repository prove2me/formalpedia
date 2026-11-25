-- Prove2me | Theorems.Thm_Arxiv1810_02867_sh_system
-- name    : Arxiv1810_02867.sh_system
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T05:17:59.218859+00:00
-- url     : https://prove2.me/theorems/dc97678f-b569-440d-99aa-60eaea693274
-- title:
--   Eqs. (A45)-(A47): horizontally polarised shear waves
-- statement:
--   Let $v,\tau,F,h$ and the parameters $\rho^o,\xi,s$ be independent of $x_2$ and satisfy (A43)-(A44). Let $\tau$ and $h$ be symmetric, $\xi_{imn}=\xi_{inm}$, and $s_{klmn}=s_{lkmn}=s_{klnm}=s_{mnkl}$ (A31). Assume $\rho^o_{21}=\rho^o_{23}=0$,
--   $$s_{1211}=s_{1222}=s_{1233}=s_{1213}=s_{3211}=s_{3222}=s_{3233}=s_{3213}=0$$
--   and
--   $$\xi_{112}=\xi_{132}=\xi_{211}=\xi_{222}=\xi_{233}=\xi_{213}=\xi_{312}=\xi_{332}=0.$$
--   Then, in the $(x_1,x_3)$-plane, $(v_2,\tau_{21},\tau_{23})$ satisfy the SH system (A45)-(A47):
--   $$\rho^o_{22}\partial_tv_2-2\xi_{221}\partial_t\tau_{21}-2\xi_{223}\partial_t\tau_{23}-\partial_1\tau_{21}-\partial_3\tau_{23}=F_2,$$
--   $$-4s_{1221}\partial_t\tau_{21}-4s_{1223}\partial_t\tau_{23}+2\xi_{221}\partial_tv_2+\partial_1v_2=2h_{21},$$
--   $$-4s_{1223}\partial_t\tau_{21}-4s_{3223}\partial_t\tau_{23}+2\xi_{223}\partial_tv_2+\partial_3v_2=2h_{23}.$$
--
--   **Formalization Note** The $x_2$-independent quantities are restricted to the plane $x_2=0$.
-- source:
--   Wapenaar and Reinicke, Unified wave field retrieval and imaging method for inhomogeneous non-reciprocal media, arXiv:1810.02867v2 (2020), claim c025; Appendix A.2, eqs. (A43)-(A47), PDF p. 25

import Mathlib
import Definitions.Def_Arxiv1810_02867_Basic

open MeasureTheory Matrix

namespace Arxiv1810_02867

theorem sh_system (rhoO : Space → Fin 3 → Fin 3 → ℝ) (xi : Space → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (s : Space → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ) (v F : Space → ℝ → Fin 3 → ℝ)
    (tau h : Space → ℝ → Fin 3 → Fin 3 → ℝ)
    (hiv : IndepX2 v) (hitau : IndepX2 tau) (hiF : IndepX2 F) (hih : IndepX2 h)
    (hirho : IndepX2 rhoO) (hixi : IndepX2 xi) (his : IndepX2 s)
    (hrho0 : ∀ x, rhoO x 1 0 = 0 ∧ rhoO x 1 2 = 0)
    (hs0 : ∀ x, s x 0 1 0 0 = 0 ∧ s x 0 1 1 1 = 0 ∧ s x 0 1 2 2 = 0 ∧ s x 0 1 0 2 = 0 ∧
      s x 2 1 0 0 = 0 ∧ s x 2 1 1 1 = 0 ∧ s x 2 1 2 2 = 0 ∧ s x 2 1 0 2 = 0)
    (hxi0 : ∀ x, xi x 0 0 1 = 0 ∧ xi x 0 2 1 = 0 ∧ xi x 1 0 0 = 0 ∧ xi x 1 1 1 = 0 ∧
      xi x 1 2 2 = 0 ∧ xi x 1 0 2 = 0 ∧ xi x 2 0 1 = 0 ∧ xi x 2 2 1 = 0)
    (hxisym : ∀ x i m n, xi x i m n = xi x i n m)
    (htau : ∀ x t i j, tau x t i j = tau x t j i) (hh : ∀ x t k l, h x t k l = h x t l k)
    (hs : ∀ x k l m n, s x k l m n = s x l k m n ∧ s x k l m n = s x k l n m ∧
      s x k l m n = s x m n k l)
    (hE : ElastoEqs rhoO xi s v tau F h) :
    SHSystem (restr rhoO) (restr xi) (restr s) (restr v) (restr tau) (restr F) (restr h) := by sorry

end Arxiv1810_02867
