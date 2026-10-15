-- Prove2me | Theorems.Thm_DynReinsDiv_HJB_lemma_A_6
-- name    : DynReinsDiv.HJB.lemma_A_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:28.558967+00:00
-- url     : https://prove2.me/theorems/3c8fe4df-0f8e-4f3c-bc86-c6b02b76f880
-- title:
--   Lemma A.6 — the penalized solution satisfies u^ε_xx ≥ 0
-- statement:
--   Fix a model, $L>0$ and the positive root $\lambda$ of $f$. There is $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0)$, every penalty function $\beta_\varepsilon$, every boundary datum $f_\varepsilon$ and every solution $u^\varepsilon\in C^{2,1}(\overline{\mathcal Q}_{L,T})$ of the penalized problem (A.17) with $u^\varepsilon\ge1$ in $\mathcal Q_{L,T}$,
--   $$u^\varepsilon_{xx}\ge0 \tag{A.30}$$
--   in $\mathcal Q_{L,T}$.
--
--   In the limit this becomes property (3.7) of Theorem 3.1: $v_{xxx}\ge0$ in the weak sense.
--
--   **Formalization Note** As in Lemma A.4, the statement is posed for every solution of (A.17) in the class of Lemma A.3 with $u^\varepsilon\ge1$.
-- source:
--   Guan, Xu & Zhou, Dynamic optimal reinsurance and dividend-payout in a finite time horizon, arXiv:2008.00391v3, p. 30, Lemma A.6

import Mathlib
import Definitions.Def_DynReinsDiv_HJB_Model
import Definitions.Def_DynReinsDiv_HJB_PDE

namespace DynReinsDiv.HJB

theorem lemma_A_6 (M : Model) (L lam : ℝ) (hL : 0 < L) (hlam : 0 < lam)
    (hroot : M.fA lam = 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ β fε : ℝ → ℝ, IsPenalty M ε β → IsRamp ε lam fε →
      ∀ u ux uxx ut : ℝ → ℝ → ℝ, IsC21RectClosed L M.T u ux uxx ut →
        SolvesPenalized M L lam β fε u ux uxx ut →
        (∀ x t : ℝ, 0 < x → x < L → 0 < t → t ≤ M.T → 1 ≤ u x t) →
        ∀ x t : ℝ, 0 < x → x < L → 0 < t → t ≤ M.T → 0 ≤ uxx x t := by sorry

end DynReinsDiv.HJB
