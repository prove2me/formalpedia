-- Prove2me | Theorems.Thm_DigitalPrivacy_Welfare_usage_driven_overcollection
-- name    : DigitalPrivacy.Welfare.usage_driven_overcollection
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T04:32:53.455133+00:00
-- url     : https://prove2.me/theorems/54d32ecc-fcfe-40ba-84f3-0673fb36b233
-- title:
--   App. A.4, p. 34 — for P = 0, a business that over-collects also over-protects
-- statement:
--   Work in the model of *DigitalPrivacy.Welfare.Setting* with a purely usage-driven business, $P=0$, under the standing assumptions $0\le\beta<1$, $0\le\rho<1$, $\psi>0$, $0<\alpha\le1$. Let $(\xi^*,C^*)$ be any business optimum and $(\xi^W,C^W)$ any social optimum. If the business over-collects relative to the planner, it also over-protects:
--   $$
--   \xi^*>\xi^W\ \Longrightarrow\ C^*>C^W.
--   $$
--
--   This is the first step of the purely usage-driven part of the proof of Theorem 2 (App. A.4), where the paper derives it "from the first-order conditions on the data collection". Combined with the argument behind (11), it rules out over-collection for $P=0$.
--
--   **Formalization Note.** The standing assumptions add $\psi>0$ and $\alpha>0$ to the paper's printed ranges, as in Theorem 2.
-- source:
--   Fainmesser, Galeotti, Momot, Digital Privacy, author manuscript (This Draft: April 2022; SSRN 3459274), p. 34, App. A.4, last paragraph (proof of Theorem 2, case P = 0)

import Mathlib
import Definitions.Def_DigitalPrivacy_Welfare_Setting

namespace DigitalPrivacy.Welfare
theorem usage_driven_overcollection (β ρ ψ α : ℝ) (h : Standing β ρ ψ 0 α) (ξs Cs ξW CW : ℝ)
    (hs : DigitalPrivacy.Strategy.IsBusinessOpt β ρ ψ 0 ξs Cs) (hW : IsSocialOpt β ρ ψ 0 α ξW CW)
    (hover : ξW < ξs) :
    CW < Cs := by sorry
end DigitalPrivacy.Welfare
