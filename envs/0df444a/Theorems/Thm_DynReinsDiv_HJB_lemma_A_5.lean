-- Prove2me | Theorems.Thm_DynReinsDiv_HJB_lemma_A_5
-- name    : DynReinsDiv.HJB.lemma_A_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:12.393387+00:00
-- url     : https://prove2.me/theorems/1a56ec03-0e64-46ce-9dee-0a54b5f88d61
-- title:
--   Lemma A.5 — the penalized solution satisfies λu^ε + u^ε_x ≥ 0
-- statement:
--   Fix a model, $L>0$ and the positive root $\lambda$ of $f$. There is $\varepsilon_0>0$ such that for every $\varepsilon\in(0,\varepsilon_0)$, every penalty function $\beta_\varepsilon$, every boundary datum $f_\varepsilon$ and every solution $u^\varepsilon\in C^{2,1}(\overline{\mathcal Q}_{L,T})$ of the penalized problem (A.17) with $u^\varepsilon\ge1$ in $\mathcal Q_{L,T}$,
--   $$\lambda u^\varepsilon+u^\varepsilon_x\ge0 \tag{A.24}$$
--   in $\mathcal Q_{L,T}$.
--
--   Together with Lemma A.3 this bounds $|u^\varepsilon_x|$ independently of $\varepsilon$, and in the limit it becomes property (3.9), $\lambda v_x+v_{xx}\ge0$, of Theorem 3.1.
--
--   **Formalization Note** As in Lemma A.4, the statement is posed for every solution of (A.17) in the class of Lemma A.3 with $u^\varepsilon\ge1$.
-- source:
--   Guan, Xu & Zhou, Dynamic optimal reinsurance and dividend-payout in a finite time horizon, arXiv:2008.00391v3, p. 29, Lemma A.5

import Mathlib
import Definitions.Def_DynReinsDiv_HJB_Model
import Definitions.Def_DynReinsDiv_HJB_PDE

namespace DynReinsDiv.HJB

theorem lemma_A_5 (M : Model) (L lam : ℝ) (hL : 0 < L) (hlam : 0 < lam)
    (hroot : M.fA lam = 0) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ β fε : ℝ → ℝ, IsPenalty M ε β → IsRamp ε lam fε →
      ∀ u ux uxx ut : ℝ → ℝ → ℝ, IsC21RectClosed L M.T u ux uxx ut →
        SolvesPenalized M L lam β fε u ux uxx ut →
        (∀ x t : ℝ, 0 < x → x < L → 0 < t → t ≤ M.T → 1 ≤ u x t) →
        ∀ x t : ℝ, 0 < x → x < L → 0 < t → t ≤ M.T → 0 ≤ lam * u x t + ux x t := by sorry

end DynReinsDiv.HJB
