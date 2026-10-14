-- Prove2me | Theorems.Thm_FakeAccounts_Defensive_prop3a_literacy
-- name    : FakeAccounts.Defensive.prop3a_literacy
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:29:16.023597+00:00
-- url     : https://prove2.me/theorems/36306b39-ddde-4683-9bea-4c1c9148f361
-- title:
--   Proposition 3(a), p. 8875 — the defensive purchase strictly decreases in social media literacy $l$
-- statement:
--   Fix model parameters in the standing ranges with $c_0>0$ and $p_0>0$, and an antifake effort $d\ge0$. Regard the H-type's defensive purchase $x_H^{csep}$ of the costly separating equilibrium as a function of social media literacy $l$, all other parameters held fixed. Then
--   $$l\ \longmapsto\ x_H^{csep}(d;\,l)\quad\text{is strictly decreasing on } (0,1).$$
--
--   Higher literacy leaves fewer uninformed consumers to deceive, which lowers the L-type's gain from mimicry and hence the H-type's need to buy fake accounts.
--
--   **Formalization Note.** $l$ is varied by a structure update of the parameter bundle. The claim is stated for every $l\in(0,1)$, not only for those $l$ at which $d\le d_2$ (i.e. $d$ is in the costly separating range); this is a strengthening of the paper's statement. $c_0>0$ makes $c>0$, needed for strictness; $p_0>0$ makes $p_f>0$. Assumptions 1–2 are not imposed.
-- source:
--   Huang and Liu, Economics of Social Media Fake Accounts, Management Science 71(10), 2025, p. 8875, Proposition 3(a)

import Mathlib
import Definitions.Def_FakeAccounts_Defensive_Setting

namespace FakeAccounts.Defensive

/-- Proposition 3(a), p. 8875: x_H^csep strictly decreases in social media literacy l ∈ (0, 1). -/
theorem prop3a_literacy (P : FakeAccounts.Platform.Params) (hP : FakeAccounts.Platform.Standing P) (hc0 : 0 < P.c0) (hp0 : 0 < P.p0) :
    ∀ d, 0 ≤ d → StrictAntiOn (fun l' => xCsepH { P with l := l' } d) (Set.Ioo 0 1) := by sorry

end FakeAccounts.Defensive
