-- Prove2me | Theorems.Thm_DigitalPrivacy_Welfare_eq_12
-- name    : DigitalPrivacy.Welfare.eq_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T04:32:53.197341+00:00
-- url     : https://prove2.me/theorems/562f54b2-7e81-4fb1-9916-0876d5773678
-- title:
--   (12), p. 34 — the planner's optimum stores weakly more user data than the business's
-- statement:
--   Work in the model of *DigitalPrivacy.Welfare.Setting* under the standing assumptions $0\le\beta<1$, $0\le\rho<1$, $\psi>0$, $0\le P\le1$, $0<\alpha\le1$. Let $(\xi^*,C^*)$ be any business optimum and $(\xi^W,C^W)$ any social optimum. If $\xi^*\le\xi^W$ and $C^*\ge C^W$, then the total amount of user data stored at the social optimum is at least that stored at the business optimum:
--   $$
--   \bar a^*(\xi^W,C^W)\,\xi^W\ \ge\ \bar a^*(\xi^*,C^*)\,\xi^*.
--   $$
--
--   This is display (12) of the proof of Theorem 2, obtained from (11) and $\xi^*\le\xi^W$. Together with $C^*\ge C^W$ it gives $\Pi^W\ge\Pi^*$, which the proof turns into a contradiction.
--
--   **Formalization Note.** Same hypotheses as (11): the contradiction assumptions $\xi^*\le\xi^W$, $C^*\ge C^W$ are kept as printed, and the standing assumptions add $\alpha>0$, $\psi>0$ to the printed ranges.
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (This Draft: April 2022; SSRN 3459274), p. 34, App. A.4, display (12)

import Mathlib
import Definitions.Def_DigitalPrivacy_Welfare_Setting

namespace DigitalPrivacy.Welfare
theorem eq_12 (β ρ ψ P α : ℝ) (h : Standing β ρ ψ P α) (ξs Cs ξW CW : ℝ)
    (hs : DigitalPrivacy.Strategy.IsBusinessOpt β ρ ψ P ξs Cs) (hW : IsSocialOpt β ρ ψ P α ξW CW)
    (hξ : ξs ≤ ξW) (hC : CW ≤ Cs) :
    DigitalPrivacy.Strategy.abar β ρ ξs Cs * ξs ≤ DigitalPrivacy.Strategy.abar β ρ ξW CW * ξW := by sorry
end DigitalPrivacy.Welfare
