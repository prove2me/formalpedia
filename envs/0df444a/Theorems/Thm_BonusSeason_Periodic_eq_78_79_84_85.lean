-- Prove2me | Theorems.Thm_BonusSeason_Periodic_eq_78_79_84_85
-- name    : BonusSeason.Periodic.eq_78_79_84_85
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:58.23417+00:00
-- url     : https://prove2.me/theorems/b42df788-3aa7-49f6-9cd5-77c6be133cca
-- title:
--   Eqs. (78)–(79), (84)–(85), proof of Lemma 3, pp. 48–49 (PDF 49–50) — unemployment and joint outside values in terms of S₁, S₂
-- statement:
--   Under the hypotheses of Lemma 3, the values of unemployment are
--   $$U_1=\frac{g_1\theta S_1+\beta g_2\theta S_2}{1-\beta^2},\qquad U_2=\frac{g_2\theta S_2+\beta g_1\theta S_1}{1-\beta^2},$$
--   and the joint outside values of an unmatched firm and worker are
--   $$U_1+V_1=\frac{h_1S_1+\beta h_2S_2}{1-\beta^2},\qquad U_2+V_2=\frac{h_2S_2+\beta h_1S_1}{1-\beta^2}.$$
--
--   These identities feed the incentive constraints of Lemma 4 and the optimality conditions in the proof of Proposition 1.
-- source:
--   Van Wesep & Waters, Bonus season: A theory of periodic labor markets and coordinated bonuses, SSRN 3124536 (version of January 13, 2021), proof of Lemma 3, pp. 48–49 (PDF 49–50), eqs. (78)–(79), (84)–(85)

import Mathlib
import Definitions.Def_BonusSeason_Periodic_Model

namespace BonusSeason.Periodic

/-- Equations (78)–(79) and (84)–(85), proof of Lemma 3, pp. 48–49: the values of
unemployment and the joint outside values in terms of the surpluses. -/
theorem eq_78_79_84_85 (P : Params) (hP : P.Standing) (m : ℝ → ℝ → ℝ) (hm : MatchingA1 m)
    (L : MarketState) (hL : L.Solves P m) (X : Values) (hX : X.Solves P L m) :
    X.U₁ = (L.g₁ P m * P.θ * X.S₁ P + P.β * L.g₂ P m * P.θ * X.S₂ P) / (1 - P.β ^ 2) ∧
    X.U₂ = (L.g₂ P m * P.θ * X.S₂ P + P.β * L.g₁ P m * P.θ * X.S₁ P) / (1 - P.β ^ 2) ∧
    X.U₁ + X.V₁ = (L.h₁ P m * X.S₁ P + P.β * L.h₂ P m * X.S₂ P) / (1 - P.β ^ 2) ∧
    X.U₂ + X.V₂ = (L.h₂ P m * X.S₂ P + P.β * L.h₁ P m * X.S₁ P) / (1 - P.β ^ 2) := by sorry
end BonusSeason.Periodic
