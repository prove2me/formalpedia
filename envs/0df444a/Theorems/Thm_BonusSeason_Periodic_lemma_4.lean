-- Prove2me | Theorems.Thm_BonusSeason_Periodic_lemma_4
-- name    : BonusSeason.Periodic.lemma_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:00.17824+00:00
-- url     : https://prove2.me/theorems/9764d2be-7f6f-4ed0-be34-67d68e00c5e7
-- title:
--   Lemma 4, pp. 25–26 (PDF 26–27) — incentive constraints (37)–(39) and signing bonuses (40)–(41) for periodic contracts
-- statement:
--   Under the hypotheses of Lemma 3, let $\{b^s_1,b^s_2,w_1,w_2\}$ be a periodic contract. It satisfies the incentive constraints (32), (35) and (36) if and only if
--   $$w_2\ge x^H+\theta g_2S_2,$$
--   $$w_1+\hat\beta w_2\ge x^L+\hat\beta[(1-p)x^L+px^H]+\theta(g_1S_1+\hat\beta g_2S_2),$$
--   $$w_1+\hat\beta w_2\le x^H+\hat\beta x^H+\theta(g_1S_1+\hat\beta g_2S_2).$$
--   Its present value for an odd-period hire equals $P_1$ iff $b^s_1=P_1-\dfrac{w_1+\hat\beta w_2}{1-\hat\beta^2(1-p)^2}$, and its present value for an even-period hire equals $P_2$ iff $b^s_2=P_2-w_2-\dfrac{\hat\beta(1-p)(w_1+\hat\beta w_2)}{1-\hat\beta^2(1-p)^2}$.
--
--   The lemma reduces the infinite family of incentive constraints to three linear inequalities in the two wages, and lets the signing bonuses absorb the bargained present value.
-- source:
--   Van Wesep & Waters, Bonus season: A theory of periodic labor markets and coordinated bonuses, SSRN 3124536 (version of January 13, 2021), pp. 25–26 (PDF 26–27), Lemma 4, eqs. (37)–(41)

import Mathlib
import Definitions.Def_BonusSeason_Periodic_Model

namespace BonusSeason.Periodic

/-- Lemma 4, pp. 25–26: for periodic contracts, the incentive constraints (32), (35), (36)
are equivalent to (37)–(39), and the present value of pay equals `P₁` (`P₂`) exactly when the
signing bonus is (40) ((41)). -/
theorem lemma_4 (P : Params) (hP : P.Standing) (m : ℝ → ℝ → ℝ) (hm : MatchingA1 m)
    (L : MarketState) (hL : L.Solves P m) (X : Values) (hX : X.Solves P L m)
    (c : PeriodicContract) :
    (IncentiveCompatible P X c ↔
      c.w₂ ≥ P.xH + P.θ * L.g₂ P m * X.S₂ P ∧
      c.w₁ + P.βhat * c.w₂ ≥ P.xL + P.βhat * ((1 - P.p) * P.xL + P.p * P.xH) +
        P.θ * (L.g₁ P m * X.S₁ P + P.βhat * L.g₂ P m * X.S₂ P) ∧
      c.w₁ + P.βhat * c.w₂ ≤ P.xH + P.βhat * P.xH +
        P.θ * (L.g₁ P m * X.S₁ P + P.βhat * L.g₂ P m * X.S₂ P)) ∧
    (pvOdd P c = X.P₁ ↔
      c.b₁ = X.P₁ - (c.w₁ + P.βhat * c.w₂) / (1 - P.βhat ^ 2 * (1 - P.p) ^ 2)) ∧
    (pvEven P c = X.P₂ ↔
      c.b₂ = X.P₂ - c.w₂ -
        P.βhat * (1 - P.p) * (c.w₁ + P.βhat * c.w₂) / (1 - P.βhat ^ 2 * (1 - P.p) ^ 2)) := by sorry
end BonusSeason.Periodic
