-- Prove2me | Theorems.Thm_Arxiv1810_02867_acoustic_constitutive_reorganisation
-- name    : Arxiv1810_02867.acoustic_constitutive_reorganisation
-- status  : Open
-- author  : @Xeroth
-- created : 2026-11-25T05:18:26.819275+00:00
-- url     : https://prove2.me/theorems/a4f13721-bae7-543d-bc62-25d445c347cc
-- title:
--   Eqs. (A48)-(A67): acoustic waves from the Willis equations
-- statement:
--   Let $\rho_{ik},S^{(2)}_{ikl},S^{(1)}_{mnp}$ be real time-independent parameters with $\rho_{ik}=\rho_{ki}$ and $S^{(2)}_{ikl}=-S^{(1)}_{kli}$ (A29), (A34). Let $K\neq0$ be the bulk modulus. Make the substitutions (A48)-(A51)
--   $$\tau_{ij}=-\delta_{ij}p,\quad e_{kl}=\tfrac13\delta_{kl}\Theta,\quad h_{kl}=\tfrac13\delta_{kl}q,\quad c_{mnpq}=\delta_{mn}\delta_{pq}K$$
--   in the elastodynamic equations (A23)-(A24) and the constitutive relations (A26)-(A27). Suppose these hold, with $v$ and $p$ differentiable in time. Then, with $\kappa=1/K$:
--
--   1. $\Theta=-\zeta_pv_p-\kappa p$ and $m_i=\rho^o_{ip}v_p+\xi_ip$ (A59), (A62), where $\zeta_p=\frac13\kappa S^{(1)}_{mmp}$, $\rho^o_{ip}=\rho_{ip}-\frac19\kappa S^{(2)}_{ill}S^{(1)}_{mmp}$ and $\xi_i=-\frac13\kappa S^{(2)}_{ill}$;
--   2. $\rho^o_{ip}=\rho^o_{pi}$ and $\xi_p=\zeta_p$ (A65);
--   3. the fields satisfy (A66)-(A67):
--   $$\rho^o_{ip}\partial_tv_p+\xi_i\partial_tp+\partial_ip=F_i,\qquad \xi_p\partial_tv_p+\kappa\partial_tp+\partial_kv_k=q.$$
--
--   **Formalization Note** As in the paper, the substituted equations (A24) and (A27) are assumed for all index pairs, not only for their traces (A54), (A57).
-- source:
--   Wapenaar and Reinicke, Unified wave field retrieval and imaging method for inhomogeneous non-reciprocal media, arXiv:1810.02867v2 (2020), claim c026; Appendix A.3, eqs. (A48)-(A67), PDF pp. 26-27

import Mathlib
import Definitions.Def_Arxiv1810_02867_Basic

open MeasureTheory Matrix

namespace Arxiv1810_02867

theorem acoustic_constitutive_reorganisation (rho : Space → Fin 3 → Fin 3 → ℝ)
    (S2 S1 : Space → Fin 3 → Fin 3 → Fin 3 → ℝ) (K : Space → ℝ)
    (mom v F : Space → ℝ → Fin 3 → ℝ) (pr Theta q : Space → ℝ → ℝ)
    (hK : ∀ x, K x ≠ 0) (hrho : ∀ x i k, rho x i k = rho x k i)
    (hS21 : ∀ x i k l, S2 x i k l = -S1 x k l i)
    (hbase : ElastoBase mom (fun x t i j => -(kd i j * pr x t))
      (fun x t k l => kd k l * Theta x t / 3) v F (fun x t k l => kd k l * q x t / 3))
    (hcon : WillisConst rho S2 S1 (fun x m n p' q' => kd m n * kd p' q' * K x) mom v
      (fun x t k l => kd k l * Theta x t / 3) (fun x t i j => -(kd i j * pr x t)))
    (hv : ∀ x j, Differentiable ℝ (fun t => v x t j))
    (hpr : ∀ x, Differentiable ℝ (fun t => pr x t)) :
    (∀ x t, Theta x t = -∑ j, zetaAc (K x) (S1 x) j * v x t j - kappaAc (K x) * pr x t) ∧
    (∀ x t i, mom x t i = ∑ j, rhoOAc (rho x) (K x) (S2 x) (S1 x) i j * v x t j +
        xiAc (K x) (S2 x) i * pr x t) ∧
    (∀ x i j, rhoOAc (rho x) (K x) (S2 x) (S1 x) i j = rhoOAc (rho x) (K x) (S2 x) (S1 x) j i) ∧
    (∀ x j, xiAc (K x) (S2 x) j = zetaAc (K x) (S1 x) j) ∧
    AcousticEqs (fun x => rhoOAc (rho x) (K x) (S2 x) (S1 x)) (fun x => xiAc (K x) (S2 x))
      (fun x => kappaAc (K x)) v pr F q := by sorry

end Arxiv1810_02867
