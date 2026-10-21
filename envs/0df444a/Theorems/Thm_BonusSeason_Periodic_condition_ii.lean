-- Prove2me | Theorems.Thm_BonusSeason_Periodic_condition_ii
-- name    : BonusSeason.Periodic.condition_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:51:12.755992+00:00
-- url     : https://prove2.me/theorems/a7482ff2-04d2-46ad-a774-420033157894
-- title:
--   Condition (ii), proof of Proposition 1, pp. 52–53 (PDF 53–54) — releasing a dissatisfied worker on cycle is optimal iff α ≥ α̲
-- statement:
--   Under the hypotheses of Lemma 3, the joint surplus of a pair is weakly higher if a dissatisfied worker quits at the end of an even period than if she stays one more cycle,
--   $$U_1+V_1\ge(1-x^H)(1+\beta(1-\delta))+\beta\delta(U_2+V_2)+\beta^2(1-\delta)(U_1+V_1),$$
--   if and only if $\alpha\ge\underline\alpha$.
--
--   This is the lower half of the characterization of when periodic turnover is optimal.
-- source:
--   Van Wesep & Waters, Bonus season: A theory of periodic labor markets and coordinated bonuses, SSRN 3124536 (version of January 13, 2021), proof of Proposition 1, pp. 52–53 (PDF 53–54), second condition and eq. (115)

import Mathlib
import Definitions.Def_BonusSeason_Periodic_Model

namespace BonusSeason.Periodic

/-- Condition (ii) of the proof of Proposition 1, pp. 52–53: releasing a dissatisfied
worker at the end of an even period is weakly better for the pair iff `α ≥ α̲`. -/
theorem condition_ii (P : Params) (hP : P.Standing) (m : ℝ → ℝ → ℝ) (hm : MatchingA1 m)
    (L : MarketState) (hL : L.Solves P m) (X : Values) (hX : X.Solves P L m) :
    X.U₁ + X.V₁ ≥ (1 - P.xH) * (1 + P.β * (1 - P.δ)) + P.β * P.δ * (X.U₂ + X.V₂) +
        P.β ^ 2 * (1 - P.δ) * (X.U₁ + X.V₁) ↔
      alphaLow P m L ≤ P.matchImportance := by sorry
end BonusSeason.Periodic
