-- Prove2me | Theorems.Thm_Arxiv1810_02867_willis_constitutive_reorganisation
-- name    : Arxiv1810_02867.willis_constitutive_reorganisation
-- status  : Proved
-- author  : @Xeroth
-- created : 2026-11-25T05:17:12.850306+00:00
-- url     : https://prove2.me/theorems/4f21c354-287e-4c3a-8f43-3b56725ce4ed
-- title:
--   Eqs. (A35)-(A44): reorganised Willis constitutive relations
-- statement:
--   Let real time-independent parameters $\rho_{ik},S^{(2)}_{ikl},S^{(1)}_{mnp},c_{mnpq},s_{klmn}$ on $\mathbb R^3$ satisfy $s_{klmn}c_{mnpq}=\frac12(\delta_{kp}\delta_{lq}+\delta_{kq}\delta_{lp})$ (A28). Assume the symmetry relations (A29)-(A34):
--   $$\rho_{ik}=\rho_{ki},\quad c_{mnpq}=c_{nmpq}=c_{mnqp}=c_{pqmn},\quad s_{klmn}=s_{lkmn}=s_{klnm}=s_{mnkl},$$
--   $$S^{(1)}_{mnp}=S^{(1)}_{nmp},\quad S^{(2)}_{ikl}=S^{(2)}_{ilk},\quad S^{(2)}_{ikl}=-S^{(1)}_{kli}.$$
--   Let $\tau,e,h$ be symmetric tensors (A25), and let $m,\tau,e,v,F,h$ satisfy (A23)-(A24) and the constitutive relations (A26)-(A27), with $v$ and $\tau$ differentiable in time. Then:
--
--   1. $e_{kl}=-\zeta_{klp}v_p+s_{klmn}\tau_{mn}$ and $m_i=\rho^o_{ip}v_p-\xi_{imn}\tau_{mn}$ (A38), (A37), where $\rho^o_{ip}=\rho_{ip}-S^{(2)}_{ikl}s_{klmn}S^{(1)}_{mnp}$, $\xi_{imn}=-S^{(2)}_{ikl}s_{klmn}$ and $\zeta_{klp}=s_{klmn}S^{(1)}_{mnp}$;
--   2. $\rho^o_{ip}=\rho^o_{pi}$, $\zeta_{klp}=\zeta_{lkp}$, $\xi_{imn}=\xi_{inm}$ and $\xi_{pkl}=\zeta_{klp}$ (A42);
--   3. the fields satisfy (A43)-(A44):
--   $$\rho^o_{ip}\partial_tv_p-\xi_{imn}\partial_t\tau_{mn}-\partial_j\tau_{ij}=F_i,\qquad -\xi_{pkl}\partial_tv_p+s_{klmn}\partial_t\tau_{mn}-\tfrac12(\partial_kv_l+\partial_lv_k)=-h_{kl}.$$
-- source:
--   Wapenaar and Reinicke, Unified wave field retrieval and imaging method for inhomogeneous non-reciprocal media, arXiv:1810.02867v2 (2020), claim c024; Appendix A.2, eqs. (A23)-(A44), PDF pp. 23-25

import Mathlib
import Definitions.Def_Arxiv1810_02867_Basic

open MeasureTheory Matrix

namespace Arxiv1810_02867

theorem willis_constitutive_reorganisation (rho : Space → Fin 3 → Fin 3 → ℝ)
    (S2 S1 : Space → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (c s : Space → Fin 3 → Fin 3 → Fin 3 → Fin 3 → ℝ)
    (mom v F : Space → ℝ → Fin 3 → ℝ) (tau e h : Space → ℝ → Fin 3 → Fin 3 → ℝ)
    (htau : ∀ x t i j, tau x t i j = tau x t j i) (he : ∀ x t k l, e x t k l = e x t l k)
    (hh : ∀ x t k l, h x t k l = h x t l k)
    (hsc : ∀ x k l p q, ∑ m, ∑ n, s x k l m n * c x m n p q =
      (1 / 2) * (kd k p * kd l q + kd k q * kd l p))
    (hrho : ∀ x i k, rho x i k = rho x k i)
    (hc : ∀ x m n p q, c x m n p q = c x n m p q ∧ c x m n p q = c x m n q p ∧
      c x m n p q = c x p q m n)
    (hs : ∀ x k l m n, s x k l m n = s x l k m n ∧ s x k l m n = s x k l n m ∧
      s x k l m n = s x m n k l)
    (hS1 : ∀ x m n p, S1 x m n p = S1 x n m p) (hS2 : ∀ x i k l, S2 x i k l = S2 x i l k)
    (hS21 : ∀ x i k l, S2 x i k l = -S1 x k l i)
    (hbase : ElastoBase mom tau e v F h) (hcon : WillisConst rho S2 S1 c mom v e tau)
    (hv : ∀ x p, Differentiable ℝ (fun t => v x t p))
    (htd : ∀ x m n, Differentiable ℝ (fun t => tau x t m n)) :
    (∀ x t k l, e x t k l = -∑ p, zetaW (s x) (S1 x) k l p * v x t p +
        ∑ m, ∑ n, s x k l m n * tau x t m n) ∧
    (∀ x t i, mom x t i = ∑ p, rhoOW (rho x) (S2 x) (s x) (S1 x) i p * v x t p -
        ∑ m, ∑ n, xiW (S2 x) (s x) i m n * tau x t m n) ∧
    (∀ x i p, rhoOW (rho x) (S2 x) (s x) (S1 x) i p = rhoOW (rho x) (S2 x) (s x) (S1 x) p i) ∧
    (∀ x k l p, zetaW (s x) (S1 x) k l p = zetaW (s x) (S1 x) l k p) ∧
    (∀ x i m n, xiW (S2 x) (s x) i m n = xiW (S2 x) (s x) i n m) ∧
    (∀ x p k l, xiW (S2 x) (s x) p k l = zetaW (s x) (S1 x) k l p) ∧
    ElastoEqs (fun x => rhoOW (rho x) (S2 x) (s x) (S1 x)) (fun x => xiW (S2 x) (s x)) s v tau
      F h := by sorry

end Arxiv1810_02867
