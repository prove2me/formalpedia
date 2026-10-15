-- Prove2me | Theorems.Thm_DynReinsDiv_HJB_lemma_A_2
-- name    : DynReinsDiv.HJB.lemma_A_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:35:30.293793+00:00
-- url     : https://prove2.me/theorems/82947b4d-cbdd-4610-8313-f21212db79eb
-- title:
--   Lemma A.2 — comparison principle for the penalized problem (A.17) between functions ≥ 1
-- statement:
--   Fix a model, $L>0$, the positive root $\lambda$ of $f$, $\varepsilon>0$ and a penalty function $\beta_\varepsilon$. Let $u_1, u_2\in C^{2,1}(\mathcal Q_{L,T})\cap C(\overline{\mathcal Q}_{L,T})$, $\mathcal Q_{L,T}=(0,L)\times(0,T]$, satisfy
--   1. $\partial_tu_1-\mathcal Tu_1+\beta_\varepsilon(u_1-1)\le\partial_tu_2-\mathcal Tu_2+\beta_\varepsilon(u_2-1)$ in $\mathcal Q_{L,T}$;
--   2. $(\lambda u_1+\partial_xu_1)(0,t)\ge(\lambda u_2+\partial_xu_2)(0,t)$ for $0<t\le T$;
--   3. $u_1(L,t)\le u_2(L,t)$ for $0<t\le T$;
--   4. $u_1(x,0)\le u_2(x,0)$ for $0<x<L$.
--
--   If $u_1,u_2\ge1$ in $\mathcal Q_{L,T}$, then
--   $$u_1(x,t)\le u_2(x,t),\qquad (x,t)\in\mathcal Q_{L,T}. \tag{A.18}$$
--
--   The comparison principle gives uniqueness of the penalized solution among functions $\ge1$ and is the tool behind the bounds of Lemma A.3 and the monotonicity in Lemma A.4.
--
--   **Formalization Note** $\partial_x u_i$ is required to be continuous up to $x=0$ so that the Robin condition is evaluated on a continuous extension.
-- source:
--   Guan, Xu & Zhou, Dynamic optimal reinsurance and dividend-payout in a finite time horizon, arXiv:2008.00391v3, p. 26, Lemma A.2

import Mathlib
import Definitions.Def_DynReinsDiv_HJB_Model
import Definitions.Def_DynReinsDiv_HJB_PDE

namespace DynReinsDiv.HJB

theorem lemma_A_2 (M : Model) (L lam ε : ℝ) (hL : 0 < L) (hlam : 0 < lam)
    (hroot : M.fA lam = 0) (hε : 0 < ε) (β : ℝ → ℝ) (hβ : IsPenalty M ε β)
    (u₁ u₁x u₁xx u₁t u₂ u₂x u₂xx u₂t : ℝ → ℝ → ℝ)
    (h₁ : IsC21Rect L M.T u₁ u₁x u₁xx u₁t) (h₂ : IsC21Rect L M.T u₂ u₂x u₂xx u₂t)
    (heq : ∀ x t : ℝ, 0 < x → x < L → 0 < t → t ≤ M.T →
      u₁t x t - M.Top (u₁xx x t) (u₁x x t) (u₁ x t) + β (u₁ x t - 1) ≤
        u₂t x t - M.Top (u₂xx x t) (u₂x x t) (u₂ x t) + β (u₂ x t - 1))
    (hrobin : ∀ t : ℝ, 0 < t → t ≤ M.T → lam * u₂ 0 t + u₂x 0 t ≤ lam * u₁ 0 t + u₁x 0 t)
    (hright : ∀ t : ℝ, 0 < t → t ≤ M.T → u₁ L t ≤ u₂ L t)
    (hinit : ∀ x : ℝ, 0 < x → x < L → u₁ x 0 ≤ u₂ x 0)
    (hge₁ : ∀ x t : ℝ, 0 < x → x < L → 0 < t → t ≤ M.T → 1 ≤ u₁ x t)
    (hge₂ : ∀ x t : ℝ, 0 < x → x < L → 0 < t → t ≤ M.T → 1 ≤ u₂ x t) :
    ∀ x t : ℝ, 0 < x → x < L → 0 < t → t ≤ M.T → u₁ x t ≤ u₂ x t := by sorry

end DynReinsDiv.HJB
