-- Prove2me | Theorems.Thm_FakeAccounts_Defensive_eq20_closed_form
-- name    : FakeAccounts.Defensive.eq20_closed_form
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:09.233052+00:00
-- url     : https://prove2.me/theorems/6130dc5c-59e1-4a22-bd1f-23187516f42e
-- title:
--   (20), p. 8872 — closed form $x_H^{csep}=\frac{1}{p_f}[\lambda_i\mu(1-l^2)-p_f l](c/q_L-c/q_H)$
-- statement:
--   Fix model parameters in the standing ranges with base price $p_0>0$, and an antifake effort $d\ge 0$. Let $p_f=p_0+d/(1-\tau)$ be the unit price of fake accounts and $c=c_0+c_1(1-\tau)d$ the cost of following. Then the H-type's defensive purchase in the costly separating equilibrium, $x_H^{csep}=n_2^{csep}-n_{in}^H$ with $n_2^{csep}$ given by (17), equals
--   $$x_H^{csep}=\frac{1}{p_f}\big[\lambda_i\mu(1-l^2)-p_f\,l\big]\left(\frac{c}{q_L}-\frac{c}{q_H}\right).$$
--
--   The bracket is the L-type's marginal gain per follower from mimicry and the last factor is the gap between the two types' follower rates; every comparative-statics statement of Proposition 3 is read off this formula.
--
--   **Formalization Note.** The identity needs $p_f\ne0$, so it is stated for $d\ge0$ under $p_0>0$, where $p_f\ge p_0>0$.
-- source:
--   Huang and Liu, Economics of Social Media Fake Accounts, Management Science 71(10), 2025, p. 8872, display (20)

import Mathlib
import Definitions.Def_FakeAccounts_Defensive_Setting

namespace FakeAccounts.Defensive

/-- (20), p. 8872: the closed form of the H-type's defensive purchase, for d ≥ 0. -/
theorem eq20_closed_form (P : FakeAccounts.Platform.Params) (hP : FakeAccounts.Platform.Standing P) (hp0 : 0 < P.p0) :
    ∀ d, 0 ≤ d → xCsepH P d = 1 / FakeAccounts.Platform.price P d * (P.lamI * P.mu * (1 - P.l ^ 2) - FakeAccounts.Platform.price P d * P.l) *
      (FakeAccounts.Platform.cost P d / P.qL - FakeAccounts.Platform.cost P d / P.qH) := by sorry

end FakeAccounts.Defensive
