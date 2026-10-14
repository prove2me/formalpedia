-- Prove2me | Theorems.Thm_FakeAccounts_Defensive_prop3a_base_price
-- name    : FakeAccounts.Defensive.prop3a_base_price
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:06.989636+00:00
-- url     : https://prove2.me/theorems/ab304d2a-1012-49b1-af36-9575756e529f
-- title:
--   Proposition 3(a), p. 8875 — the defensive purchase strictly decreases in the base price $p_0$
-- statement:
--   Fix model parameters in the standing ranges with $c_0>0$, and an antifake effort $d\ge0$. Regard the H-type's defensive purchase $x_H^{csep}$ as a function of the base price of fake accounts $p_0$, all other parameters held fixed. Then
--   $$p_0\ \longmapsto\ x_H^{csep}(d;\,p_0)\quad\text{is strictly decreasing on } (0,\infty).$$
--
--   A higher base price makes each fake account dearer and lowers the L-type's net gain from mimicry; both reduce defensive purchasing.
--
--   **Formalization Note.** $p_0$ is varied by a structure update. The claim holds for every $p_0>0$, including values with $d>d_2$ (outside the costly separating range); this is a strengthening. $c_0>0$ is needed for strictness.
-- source:
--   Huang and Liu, Economics of Social Media Fake Accounts, Management Science 71(10), 2025, p. 8875, Proposition 3(a)

import Mathlib
import Definitions.Def_FakeAccounts_Defensive_Setting

namespace FakeAccounts.Defensive

/-- Proposition 3(a), p. 8875: x_H^csep strictly decreases in the base price p₀ > 0. -/
theorem prop3a_base_price (P : FakeAccounts.Platform.Params) (hP : FakeAccounts.Platform.Standing P) (hc0 : 0 < P.c0) :
    ∀ d, 0 ≤ d → StrictAntiOn (fun p => xCsepH { P with p0 := p } d) (Set.Ioi 0) := by sorry

end FakeAccounts.Defensive
