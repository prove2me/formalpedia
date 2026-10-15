-- Prove2me | Theorems.Thm_DynReinsDiv_HJB_lemma_A_4
-- name    : DynReinsDiv.HJB.lemma_A_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:15.012793+00:00
-- url     : https://prove2.me/theorems/e9596452-2cef-41ac-a969-14231936010c
-- title:
--   Lemma A.4 — the penalized solution satisfies u^ε_t ≥ 0 and u^ε_x ≤ 0
-- statement:
--   Fix a model, $L>0$ and the positive root $\lambda$ of $f$. There is $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0)$, every penalty function $\beta_\varepsilon$, every boundary datum $f_\varepsilon$ and every solution $u^\varepsilon\in C^{2,1}(\overline{\mathcal Q}_{L,T})$ of the penalized problem (A.17) with $u^\varepsilon\ge1$ in $\mathcal Q_{L,T}$,
--   $$u^\varepsilon_t\ge0, \tag{A.20}$$
--   $$u^\varepsilon_x\le0 \tag{A.21}$$
--   in $\mathcal Q_{L,T}=(0,L)\times(0,T]$.
--
--   In the limit these become $v_t\ge0$ and $v_{xx}\le0$, properties (3.5) and (3.6) of Theorem 3.1.
--
--   **Formalization Note** The paper's $u^\varepsilon$ is the solution of Lemma A.3, which satisfies $u^\varepsilon\ge1$ for small $\varepsilon$; by Lemma A.2 it is the only solution with this property. The statement is posed for every such solution.
-- source:
--   Guan, Xu & Zhou, Dynamic optimal reinsurance and dividend-payout in a finite time horizon, arXiv:2008.00391v3, p. 28, Lemma A.4

import Mathlib
import Definitions.Def_DynReinsDiv_HJB_Model
import Definitions.Def_DynReinsDiv_HJB_PDE

namespace DynReinsDiv.HJB

theorem lemma_A_4 (M : Model) (L lam : ℝ) (hL : 0 < L) (hlam : 0 < lam)
    (hroot : M.fA lam = 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ β fε : ℝ → ℝ, IsPenalty M ε β → IsRamp ε lam fε →
      ∀ u ux uxx ut : ℝ → ℝ → ℝ, IsC21RectClosed L M.T u ux uxx ut →
        SolvesPenalized M L lam β fε u ux uxx ut →
        (∀ x t : ℝ, 0 < x → x < L → 0 < t → t ≤ M.T → 1 ≤ u x t) →
        ∀ x t : ℝ, 0 < x → x < L → 0 < t → t ≤ M.T → 0 ≤ ut x t ∧ ux x t ≤ 0 := by sorry

end DynReinsDiv.HJB
