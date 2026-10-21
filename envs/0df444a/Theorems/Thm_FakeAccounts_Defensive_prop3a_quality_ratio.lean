-- Prove2me | Theorems.Thm_FakeAccounts_Defensive_prop3a_quality_ratio
-- name    : FakeAccounts.Defensive.prop3a_quality_ratio
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:14.841966+00:00
-- url     : https://prove2.me/theorems/183d9bec-db1e-4082-b78a-59eefd716288
-- title:
--   Proposition 3(a), p. 8875 — the defensive purchase strictly decreases in the quality ratio $R=q_L/q_H$
-- statement:
--   Fix model parameters in the standing ranges with $c_0>0$ and $p_0>0$, and an antifake effort $d$ with $0\le d<d_2=(1-\tau)(\eta_2-p_0)$. Hold $q_H$ fixed and set $q_L=R\,q_H$. Then
--   $$R\ \longmapsto\ x_H^{csep}(d;\,q_L=Rq_H)\quad\text{is strictly decreasing on } (0,1).$$
--
--   A higher quality ratio narrows the gap between the two types' follower counts, so the H-type needs fewer fake accounts to separate.
--
--   **Formalization Note.** The paper never defines $R$; the text after Proposition 3 says "increasing the quality ratio $q_L/q_H$", so $R=q_L/q_H$ with $q_H$ fixed. $d<d_2$ is needed: at $d=d_2$ the purchase is $0$ for every $R$, so only weak monotonicity holds there. $d_2$ does not depend on $q_L$. $c_0>0$ is needed for strictness.
-- source:
--   Huang and Liu, Economics of Social Media Fake Accounts, Management Science 71(10), 2025, p. 8875, Proposition 3(a), and the sentence 'Increasing the quality ratio qL/qH …'

import Mathlib
import Definitions.Def_FakeAccounts_Defensive_Setting

namespace FakeAccounts.Defensive

/-- Proposition 3(a), p. 8875: x_H^csep strictly decreases in the quality ratio
R = q_L/q_H ∈ (0, 1), q_H fixed, for 0 ≤ d < d₂. -/
theorem prop3a_quality_ratio (P : FakeAccounts.Platform.Params) (hP : FakeAccounts.Platform.Standing P) (hc0 : 0 < P.c0) (hp0 : 0 < P.p0) :
    ∀ d, 0 ≤ d → d < FakeAccounts.Platform.d2 P →
      StrictAntiOn (fun R => xCsepH { P with qL := R * P.qH } d) (Set.Ioo 0 1) := by sorry

end FakeAccounts.Defensive
