-- Prove2me | Theorems.Thm_BonusSeason_Periodic_lemma_3
-- name    : BonusSeason.Periodic.lemma_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:05.425594+00:00
-- url     : https://prove2.me/theorems/f8951da3-a891-45af-af7f-86f30b3e758f
-- title:
--   Lemma 3, p. 23 (PDF 24) — closed forms (26)–(29) for the surpluses S₁, S₂ and the present values of pay P₁, P₂
-- statement:
--   Assume the standing assumptions and A1, let the market state solve the periodic market equations, and let the values solve (16)–(25). With $h_s=\theta g_s+(1-\theta)f_s$ and $\hat\beta=\beta(1-\delta)$, the surpluses are
--   $$S_1=\frac{(1-x^L)(1-\hat\beta h_2)+\hat\beta\big((1-p)(1-x^L)+p(1-x^H)\big)}{1-\hat\beta^2(1-p)(1-h_1)(1-p-h_2)},\qquad S_2=\frac{1-x^L+\hat\beta(1-p)(1-h_1)\big(1-x^L+\hat\beta p(1-x^H)\big)}{1-\hat\beta^2(1-p)(1-h_1)(1-p-h_2)},$$
--   and the present values of pay are
--   $$P_1=\frac{x^L+\hat\beta\big((1-p)x^L+px^H\big)+\theta\big[g_1S_1+\hat\beta g_2S_2+[1-\hat\beta^2(1-p)^2](1-g_1)S_1\big]}{1-\hat\beta^2(1-p)^2},\qquad P_2=x^L+\theta\big[S_2-\hat\beta(1-p)(1-g_1)S_1\big]+\hat\beta(1-p)P_1.$$
--
--   These closed forms make the bargained pay and the match surpluses explicit functions of the parameters and of the matching likelihoods.
--
--   **Formalization Note** Formula (29) holds with equation (21) in its δ-corrected form (see the model definition).
-- source:
--   Van Wesep & Waters, Bonus season: A theory of periodic labor markets and coordinated bonuses, SSRN 3124536 (version of January 13, 2021), p. 23 (PDF 24), Lemma 3, eqs. (26)–(29)

import Mathlib
import Definitions.Def_BonusSeason_Periodic_Model

namespace BonusSeason.Periodic

/-- Lemma 3, p. 23: the surpluses (26)–(27) and the present values of pay (28)–(29). -/
theorem lemma_3 (P : Params) (hP : P.Standing) (m : ℝ → ℝ → ℝ) (hm : MatchingA1 m)
    (L : MarketState) (hL : L.Solves P m) (X : Values) (hX : X.Solves P L m) :
    X.S₁ P = ((1 - P.xL) * (1 - P.βhat * L.h₂ P m) +
        P.βhat * ((1 - P.p) * (1 - P.xL) + P.p * (1 - P.xH))) /
      (1 - P.βhat ^ 2 * (1 - P.p) * (1 - L.h₁ P m) * (1 - P.p - L.h₂ P m)) ∧
    X.S₂ P = (1 - P.xL + P.βhat * (1 - P.p) * (1 - L.h₁ P m) *
        (1 - P.xL + P.βhat * P.p * (1 - P.xH))) /
      (1 - P.βhat ^ 2 * (1 - P.p) * (1 - L.h₁ P m) * (1 - P.p - L.h₂ P m)) ∧
    X.P₁ = (P.xL + P.βhat * ((1 - P.p) * P.xL + P.p * P.xH) +
        P.θ * (L.g₁ P m * X.S₁ P + P.βhat * L.g₂ P m * X.S₂ P +
          (1 - P.βhat ^ 2 * (1 - P.p) ^ 2) * (1 - L.g₁ P m) * X.S₁ P)) /
      (1 - P.βhat ^ 2 * (1 - P.p) ^ 2) ∧
    X.P₂ = P.xL + P.θ * (X.S₂ P - P.βhat * (1 - P.p) * (1 - L.g₁ P m) * X.S₁ P) +
      P.βhat * (1 - P.p) * X.P₁ := by sorry
end BonusSeason.Periodic
