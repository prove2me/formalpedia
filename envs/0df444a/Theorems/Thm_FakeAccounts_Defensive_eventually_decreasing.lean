-- Prove2me | Theorems.Thm_FakeAccounts_Defensive_eventually_decreasing
-- name    : FakeAccounts.Defensive.eventually_decreasing
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:05.024036+00:00
-- url     : https://prove2.me/theorems/31bc1d7d-6eab-4c97-9311-911162105e40
-- title:
--   p. 8875 — $m_2$ vanishes at $d_2$ and the defensive purchase falls on a left neighbourhood of $d_2$
-- statement:
--   Fix model parameters in the standing ranges with $c_0>0$, $p_0>0$ and Assumption 3, $p_0<\eta_2=\frac1l\lambda_i\mu(1-l^2)$. Let $d_2=(1-\tau)(\eta_2-p_0)$ be the upper end of the costly separating range. Then
--
--   1. at $d=d_2$ the fake-account price is $p_f=\eta_2$, so the L-type's marginal gain from mimicry vanishes:
--   $$\lambda_i\mu(1-l^2)-p_f(d_2)\,l=0,$$
--   and hence the nuisance cost effect $m_2$ is $0$ there;
--   2. there is $\varepsilon>0$ such that $x_H^{csep}$ is strictly decreasing on $[d_2-\varepsilon,\,d_2]$.
--
--   This is the precise content of the paper's remark that as $d$ increases "$m_2\to0$" and the negative effect $m_1$ eventually dominates.
--
--   **Formalization Note.** As $d\to\infty$, $m_2$ does not tend to $0$ (it tends to $-c_1(1-\tau)l(q_H-q_L)/(q_Hq_L)$); the remark is true within the costly separating range, which ends at $d_2$, and that is what is stated. $c_0>0$ makes $c>0$ (so $m_1<0$ at $d_2$); $p_0>0$ and Assumption 3 give $0<d_2$ and $p_f>0$.
-- source:
--   Huang and Liu, Economics of Social Media Fake Accounts, Management Science 71(10), 2025, p. 8875, right column, paragraph after the display of m₂

import Mathlib
import Definitions.Def_FakeAccounts_Defensive_Setting

namespace FakeAccounts.Defensive

/-- p. 8875: m₂ vanishes at d₂ (p_f = η₂) and x_H^csep is strictly decreasing on a
left neighbourhood [d₂ − ε, d₂] of d₂. -/
theorem eventually_decreasing (P : FakeAccounts.Platform.Params) (hP : FakeAccounts.Platform.Standing P) (hc0 : 0 < P.c0) (hp0 : 0 < P.p0)
    (hA3 : P.p0 < FakeAccounts.Platform.eta2 P) :
    P.lamI * P.mu * (1 - P.l ^ 2) - FakeAccounts.Platform.price P (FakeAccounts.Platform.d2 P) * P.l = 0 ∧
      ∃ ε > 0, StrictAntiOn (xCsepH P) (Set.Icc (FakeAccounts.Platform.d2 P - ε) (FakeAccounts.Platform.d2 P)) := by sorry

end FakeAccounts.Defensive
