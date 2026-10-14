-- Prove2me | Theorems.Thm_FakeAccounts_Defensive_marginal_effects
-- name    : FakeAccounts.Defensive.marginal_effects
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:09.017945+00:00
-- url     : https://prove2.me/theorems/5569f9dd-4f0d-4ebf-a4c7-3a8862753000
-- title:
--   p. 8875 — $dx_H^{csep}/dd=m_1+m_2$, the fake-account-price and nuisance-cost marginal effects
-- statement:
--   Fix model parameters in the standing ranges with $p_0>0$, and $d\ge0$. Write $p_f=p_0+d/(1-\tau)$ and $c=c_0+c_1(1-\tau)d$, and let
--   $$m_1=-\frac{1}{1-\tau}\,\frac{\lambda_i\mu(1-l^2)}{p_f^2}\,\frac{q_H-q_L}{q_Hq_L}\,c,\qquad m_2=c_1(1-\tau)\,\frac{\lambda_i\mu(1-l^2)-p_f l}{p_f}\,\frac{q_H-q_L}{q_Hq_L}.$$
--   Then the H-type's defensive purchase $d\mapsto x_H^{csep}(d)$ is differentiable at $d$ with derivative
--   $$\frac{d\,x_H^{csep}}{dd}=m_1+m_2 .$$
--
--   The paper calls $m_1$ the higher fake-account price effect and $m_2$ the higher nuisance cost effect; the sign of their sum decides whether the purchase rises or falls in the antifake effort (Proposition 3(c)).
--
--   **Formalization Note.** The page names $m_1$ and $m_2$ as marginal effects without writing $dx/dd=m_1+m_2$; the statement makes that explicit. No signs of $m_1,m_2$ are asserted. $p_0>0$ and $d\ge0$ make $p_f>0$.
-- source:
--   Huang and Liu, Economics of Social Media Fake Accounts, Management Science 71(10), 2025, p. 8875, displays defining m₁ and m₂

import Mathlib
import Definitions.Def_FakeAccounts_Defensive_Setting

namespace FakeAccounts.Defensive

/-- p. 8875: dx_H^csep/dd = m₁ + m₂ at every d ≥ 0. -/
theorem marginal_effects (P : FakeAccounts.Platform.Params) (hP : FakeAccounts.Platform.Standing P) (hp0 : 0 < P.p0) :
    ∀ d, 0 ≤ d → HasDerivAt (xCsepH P)
      (-(1 / (1 - P.tau)) * (P.lamI * P.mu * (1 - P.l ^ 2) / FakeAccounts.Platform.price P d ^ 2) *
          ((P.qH - P.qL) / (P.qH * P.qL)) * FakeAccounts.Platform.cost P d
        + P.c1 * (1 - P.tau) * ((P.lamI * P.mu * (1 - P.l ^ 2) - FakeAccounts.Platform.price P d * P.l) / FakeAccounts.Platform.price P d) *
          ((P.qH - P.qL) / (P.qH * P.qL))) d := by sorry

end FakeAccounts.Defensive
