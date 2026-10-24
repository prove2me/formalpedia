-- Prove2me | Theorems.Thm_DynReinsDiv_HJB_eq_A_21
-- name    : DynReinsDiv.HJB.eq_A_21
-- status  : Open
-- author  : @tianyipeng
-- created : 2026-10-23T21:58:08.087922+00:00
-- url     : https://prove2.me/theorems/97e05336-5bd2-478e-b169-cbec0f443c21
-- title:
--   Lemma A.4, (A.21) — the penalized solution satisfies u^ε_x ≤ 0
-- statement:
--   Fix a model, $L>0$ and the positive root $\lambda$ of $f$ (A.12). There is $\varepsilon_0>0$ with the following property. Let $\varepsilon\in(0,\varepsilon_0)$, let $\beta_\varepsilon$ be a penalty function and $f_\varepsilon$ a boundary datum as on pp. 24–25, and let $u^\varepsilon\in C^{2,1}(\overline{\mathcal Q}_{L,T})$ solve the penalized problem (A.17)
--   $$u_t-\mathcal T u+\beta_\varepsilon(u-1)=0\ \text{in }\mathcal Q_{L,T},\quad (\lambda u+u_x)(0,t)=f_\varepsilon(t),\quad u(L,t)=1,\quad u(x,0)=1,$$
--   with $u^\varepsilon\ge1$ in $\mathcal Q_{L,T}=(0,L)\times(0,T]$. Then
--   $$u^\varepsilon_x\le 0\quad\text{in }\mathcal Q_{L,T}. \tag{A.21}$$
--
--   This is the second half of Lemma A.4. Together with (A.20), $u^\varepsilon_t\ge0$, it gives Lemma A.4. In the limit $\varepsilon\to0$ it becomes the concavity $v_{xx}\le 0$ of the value function, property (3.6) of Theorem 3.1.
--
--   **Formalization Note** The hypotheses are exactly those of the milestone `DynReinsDiv.HJB.lemma_A_4`, and the conclusion is its second conjunct. The derivative $u_x$ is the explicit function `ux`, continuous on the closed rectangle.
-- source:
--   Guan, Xu & Zhou, Dynamic optimal reinsurance and dividend-payout in a finite time horizon, arXiv:2008.00391v3, p. 28, Lemma A.4, inequality (A.21) and its proof

import Mathlib
import Definitions.Def_DynReinsDiv_HJB_Model
import Definitions.Def_DynReinsDiv_HJB_PDE

namespace DynReinsDiv.HJB

theorem eq_A_21 (M : Model) (L lam : ℝ) (hL : 0 < L) (hlam : 0 < lam)
    (hroot : M.fA lam = 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ β fε : ℝ → ℝ, IsPenalty M ε β → IsRamp ε lam fε →
      ∀ u ux uxx ut : ℝ → ℝ → ℝ, IsC21RectClosed L M.T u ux uxx ut →
        SolvesPenalized M L lam β fε u ux uxx ut →
        (∀ x t : ℝ, 0 < x → x < L → 0 < t → t ≤ M.T → 1 ≤ u x t) →
        ∀ x t : ℝ, 0 < x → x < L → 0 < t → t ≤ M.T → ux x t ≤ 0 := by sorry

end DynReinsDiv.HJB
