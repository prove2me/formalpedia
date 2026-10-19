-- Prove2me | Theorems.Thm_DigitalPrivacy_Welfare_eq_11
-- name    : DigitalPrivacy.Welfare.eq_11
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:32:44.711891+00:00
-- url     : https://prove2.me/theorems/74cd6ab3-8804-4b69-840b-920c55b34190
-- title:
--   (11), p. 34 — the planner's optimum induces weakly higher user activity than the business's
-- statement:
--   Work in the model of *DigitalPrivacy.Welfare.Setting* under the standing assumptions $0\le\beta<1$, $0\le\rho<1$, $\psi>0$, $0\le P\le1$, $0<\alpha\le1$. Let $(\xi^*,C^*)$ be any business optimum (a feasible maximizer of the profit $\Pi$) and $(\xi^W,C^W)$ any social optimum (a feasible maximizer of $W=\alpha\,\mathrm{CS}+(1-\alpha)\Pi$). If $\xi^*\le\xi^W$ and $C^*\ge C^W$, then the equilibrium user activity at the social optimum is at least that at the business optimum:
--   $$
--   \bar a^*(\xi^W,C^W)\ \ge\ \bar a^*(\xi^*,C^*).
--   $$
--
--   This is display (11) of the proof of Theorem 2, derived there from $W^*\le W^W$ and $\Pi^*\ge\Pi^W$ under the contradiction assumption $\xi^*\le\xi^W$, $C^*\ge C^W$. It is the first step towards ruling out under-collection together with over-protection.
--
--   **Formalization Note.** The two contradiction assumptions are kept as hypotheses, as printed. The standing assumptions include $\alpha>0$ and $\psi>0$, which are not in the paper's printed ranges ($\alpha\in[0,1]$, $\psi\ge0$); with $\alpha=0$ the welfare objective equals the profit and (11) does not follow.
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (This Draft: April 2022; SSRN 3459274), p. 34, App. A.4, display (11)

import Mathlib
import Definitions.Def_DigitalPrivacy_Welfare_Setting

namespace DigitalPrivacy.Welfare
theorem eq_11 (β ρ ψ P α : ℝ) (h : Standing β ρ ψ P α) (ξs Cs ξW CW : ℝ)
    (hs : DigitalPrivacy.Strategy.IsBusinessOpt β ρ ψ P ξs Cs) (hW : IsSocialOpt β ρ ψ P α ξW CW)
    (hξ : ξs ≤ ξW) (hC : CW ≤ Cs) :
    DigitalPrivacy.Strategy.abar β ρ ξs Cs ≤ DigitalPrivacy.Strategy.abar β ρ ξW CW := by sorry
end DigitalPrivacy.Welfare
