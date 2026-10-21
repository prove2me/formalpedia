-- Prove2me | Theorems.Thm_BonusSeason_Periodic_condition_i
-- name    : BonusSeason.Periodic.condition_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T12:50:58.832397+00:00
-- url     : https://prove2.me/theorems/51d9955e-d56a-4fd9-b751-6f82b7336259
-- title:
--   Condition (i), proof of Proposition 1, p. 52 (PDF 53) — retaining a dissatisfied worker off cycle is optimal iff α ≤ ᾱ
-- statement:
--   Under the hypotheses of Lemma 3, the joint surplus of a pair is weakly higher if a dissatisfied worker stays at the end of an odd period than if she quits,
--   $$1-x^H+\beta(U_1+V_1)\ge U_2+V_2,$$
--   if and only if the importance of match quality satisfies $\alpha\le\overline\alpha$.
--
--   This is the upper half of the characterization of when periodic turnover is optimal.
-- source:
--   Van Wesep & Waters, Bonus season: A theory of periodic labor markets and coordinated bonuses, SSRN 3124536 (version of January 13, 2021), proof of Proposition 1, p. 52 (PDF 53), first condition and eq. (44)

import Mathlib
import Definitions.Def_BonusSeason_Periodic_Model

namespace BonusSeason.Periodic

/-- Condition (i) of the proof of Proposition 1, p. 52: keeping a dissatisfied worker at
the end of an odd period is weakly better for the pair iff `α ≤ ᾱ`. -/
theorem condition_i (P : Params) (hP : P.Standing) (m : ℝ → ℝ → ℝ) (hm : MatchingA1 m)
    (L : MarketState) (hL : L.Solves P m) (X : Values) (hX : X.Solves P L m) :
    1 - P.xH + P.β * (X.U₁ + X.V₁) ≥ X.U₂ + X.V₂ ↔ P.matchImportance ≤ alphaHigh P m L := by sorry
end BonusSeason.Periodic
