-- Prove2me | Theorems.Thm_FakeAccounts_Defensive_prop3b_bargaining
-- name    : FakeAccounts.Defensive.prop3b_bargaining
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:00.895412+00:00
-- url     : https://prove2.me/theorems/6dbda7b5-5de5-43a8-8af2-293edab89e56
-- title:
--   Proposition 3(b), p. 8875 — the defensive purchase strictly increases in the influencer's bargaining power $\lambda_i$
-- statement:
--   Fix model parameters in the standing ranges with $c_0>0$ and $p_0>0$, and an antifake effort $d\ge0$. Regard the H-type's defensive purchase $x_H^{csep}$ as a function of the influencer's revenue share $\lambda_i$, all other parameters held fixed. Then
--   $$\lambda_i\ \longmapsto\ x_H^{csep}(d;\,\lambda_i)\quad\text{is strictly increasing on } (0,\infty).$$
--
--   A larger revenue share raises the L-type's marginal gain per follower from mimicry, so the H-type must buy more fake accounts to deter it.
--
--   **Formalization Note.** $\lambda_i$ is varied by a structure update; the claim is stated for every $\lambda_i>0$, without requiring $\lambda_i+\lambda_p<1$ or $d\le d_2$ at the new value; this is a strengthening. $c_0>0$ is needed for strictness and $p_0>0$ for $p_f>0$.
-- source:
--   Huang and Liu, Economics of Social Media Fake Accounts, Management Science 71(10), 2025, p. 8875, Proposition 3(b)

import Mathlib
import Definitions.Def_FakeAccounts_Defensive_Setting

namespace FakeAccounts.Defensive

/-- Proposition 3(b), p. 8875: x_H^csep strictly increases in the bargaining power λ_i > 0. -/
theorem prop3b_bargaining (P : FakeAccounts.Platform.Params) (hP : FakeAccounts.Platform.Standing P) (hc0 : 0 < P.c0) (hp0 : 0 < P.p0) :
    ∀ d, 0 ≤ d → StrictMonoOn (fun a => xCsepH { P with lamI := a } d) (Set.Ioi 0) := by sorry

end FakeAccounts.Defensive
