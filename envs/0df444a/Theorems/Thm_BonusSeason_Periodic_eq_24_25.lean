-- Prove2me | Theorems.Thm_BonusSeason_Periodic_eq_24_25
-- name    : BonusSeason.Periodic.eq_24_25
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:15.228411+00:00
-- url     : https://prove2.me/theorems/d335939d-91be-4960-9045-1baa575e9bf4
-- title:
--   Eqs. (24)–(25), p. 22 (PDF 23) — the Nash-bargained transfers are P₁ = βU₂ − W₁ + θS₁ and P₂ = βU₁ − W₂ + θS₂
-- statement:
--   Let $0<\theta<1$ and let $J_s,V_s,W_s,U_s,P_s$ be any real numbers, with surpluses $S_1=J_1-\beta V_2+W_1-\beta U_2$ and $S_2=J_2-\beta V_1+W_2-\beta U_1$. The transfer $P_1$ maximizes the generalized Nash product
--   $$(W_1+P-\beta U_2)^{\theta}\,(J_1-P-\beta V_2)^{1-\theta}$$
--   over all transfers $P$ that leave both sides at least their outside options if and only if $S_1\ge0$ and
--   $$P_1=\beta U_2-W_1+\theta S_1,$$
--   and likewise $P_2$ is the Nash transfer for an even-period match iff $S_2\ge0$ and $P_2=\beta U_1-W_2+\theta S_2$.
--
--   The worker receives her outside option plus the share $\theta$ of the match surplus.
--
--   **Formalization Note** The page says "it immediately follows"; the condition $S_s\ge0$ makes explicit when the maximization has a solution.
-- source:
--   Van Wesep & Waters, Bonus season: A theory of periodic labor markets and coordinated bonuses, SSRN 3124536 (version of January 13, 2021), p. 22 (PDF 23), eqs. (24)–(25)

import Mathlib
import Definitions.Def_BonusSeason_Periodic_Model

namespace BonusSeason.Periodic

/-- Equations (24)–(25), p. 22: the generalized Nash bargaining transfers are
`P₁ = βU₂ − W₁ + θS₁` and `P₂ = βU₁ − W₂ + θS₂`; a maximizer exists exactly when the surplus is
nonnegative. -/
theorem eq_24_25 (P : Params) (hθ0 : 0 < P.θ) (hθ1 : P.θ < 1) (X : Values) :
    (IsNashTransfer P.θ (X.W₁ - P.β * X.U₂) (X.J₁ - P.β * X.V₂) X.P₁ ↔
      0 ≤ X.S₁ P ∧ X.P₁ = P.β * X.U₂ - X.W₁ + P.θ * X.S₁ P) ∧
    (IsNashTransfer P.θ (X.W₂ - P.β * X.U₁) (X.J₂ - P.β * X.V₁) X.P₂ ↔
      0 ≤ X.S₂ P ∧ X.P₂ = P.β * X.U₁ - X.W₂ + P.θ * X.S₂ P) := by sorry
end BonusSeason.Periodic
