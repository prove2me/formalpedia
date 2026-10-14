-- Prove2me | Theorems.Thm_FakeAccounts_Defensive_prop3a_technology
-- name    : FakeAccounts.Defensive.prop3a_technology
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:22.372664+00:00
-- url     : https://prove2.me/theorems/2d0afcfd-47c7-4d07-a497-b7cb3d16591c
-- title:
--   Proposition 3(a), p. 8875 — the defensive purchase strictly decreases in the antifake technology level $\tau$
-- statement:
--   Fix model parameters in the standing ranges with $c_0>0$ and $p_0>0$, and an antifake effort $d>0$. Let $0\le\tau_1<\tau_2<1$ be two technology levels such that $d$ is in the costly separating range at $\tau_2$, i.e.
--   $$p_f(\tau_2)=p_0+\frac{d}{1-\tau_2}\le\eta_2 .$$
--   Then the H-type's defensive purchase is strictly smaller at $\tau_2$:
--   $$x_H^{csep}(d;\,\tau_2)<x_H^{csep}(d;\,\tau_1).$$
--
--   Better antifake technology raises the price of fake accounts and lowers the consumers' nuisance cost, which narrows the follower gap; both reduce defensive purchasing.
--
--   **Formalization Note.** $\tau$ is varied by a structure update. $d>0$ is needed: at $d=0$ the purchase does not depend on $\tau$. The bound $p_f(\tau_2)\le\eta_2$ is $d\le d_2$ at $\tau_2$ (Lemma 2, (19)); $\eta_2$ does not depend on $\tau$, and the bound then also holds at $\tau_1$. Outside the costly separating range the bracket of (20) is negative and the claim can fail. $c_0>0$ makes $c>0$; $p_0>0$ makes $p_f>0$.
-- source:
--   Huang and Liu, Economics of Social Media Fake Accounts, Management Science 71(10), 2025, p. 8875, Proposition 3(a); range (19), p. 8872

import Mathlib
import Definitions.Def_FakeAccounts_Defensive_Setting

namespace FakeAccounts.Defensive

/-- Proposition 3(a), p. 8875: x_H^csep strictly decreases in the technology level τ, for
d > 0 and within the costly separating range p_f ≤ η₂. -/
theorem prop3a_technology (P : FakeAccounts.Platform.Params) (hP : FakeAccounts.Platform.Standing P) (hc0 : 0 < P.c0) (hp0 : 0 < P.p0) :
    ∀ d, 0 < d → ∀ t₁ t₂, 0 ≤ t₁ → t₁ < t₂ → t₂ < 1 → FakeAccounts.Platform.price { P with tau := t₂ } d ≤ FakeAccounts.Platform.eta2 P →
      xCsepH { P with tau := t₂ } d < xCsepH { P with tau := t₁ } d := by sorry

end FakeAccounts.Defensive
