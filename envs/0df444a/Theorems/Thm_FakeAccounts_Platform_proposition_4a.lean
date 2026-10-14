-- Prove2me | Theorems.Thm_FakeAccounts_Platform_proposition_4a
-- name    : FakeAccounts.Platform.proposition_4a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:11:15.375867+00:00
-- url     : https://prove2.me/theorems/6a5a8671-8e99-4591-9e8b-f3d959d56e86
-- title:
--   Proposition 4(a), p. 8877 — a purely profit-driven platform's equilibrium profit is uniquely maximized at zero antifake effort
-- statement:
--   Let $\pi_p(d)=\pi^{r(d)}_p(d)$ be the platform's profit in the equilibrium that its antifake effort $d$ induces, where $r(d)$ is the globally undefeated equilibrium type of Proposition 1 and $\pi^r_p$ is the profit (6). Under the standing parameter ranges, zero effort is optimal among all feasible efforts $d\ge 0$, and it is the unique optimum:
--   $$\pi_p(d)\le\pi_p(0)\ \text{ for all } d\ge 0,\qquad \pi_p(d)<\pi_p(0)\ \text{ for all } d>0.$$
--
--   This is Proposition 4(a): a purely profit-driven platform ($w=0$) optimally chooses zero antifake effort. It shows that antifake effort by a platform must be motivated by consumer welfare, not by advertising profit.
--
--   **Formalization Note** With $w=0$ the platform's objective (3), $\Pi_p=(1-w)\pi_p+wU$, is $\pi_p$, so consumer welfare $U$ does not enter. Assumption 3 is not needed and not assumed; Assumptions 1–2 are not imposed. The equilibrium type at each $d$ is Proposition 1, taken as a definition (see the Setting).
-- source:
--   Huang and Liu, Economics of Social Media Fake Accounts, Management Science 71(10), 2025, p. 8877, Proposition 4(a); (3), p. 8869

import Mathlib
import Definitions.Def_FakeAccounts_Platform_Setting

namespace FakeAccounts.Platform

/-- Proposition 4(a), p. 8877: a purely profit-driven platform (w = 0) optimally chooses zero
antifake effort; zero is the unique maximizer of its equilibrium profit over d ≥ 0. -/
theorem proposition_4a (P : Params) (hP : Standing P) :
    IsMaxOn (eqProfit P) (Set.Ici 0) 0 ∧ ∀ d, 0 < d → eqProfit P d < eqProfit P 0 := by sorry

end FakeAccounts.Platform
