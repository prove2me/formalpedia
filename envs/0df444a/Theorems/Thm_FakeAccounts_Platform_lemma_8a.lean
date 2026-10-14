-- Prove2me | Theorems.Thm_FakeAccounts_Platform_lemma_8a
-- name    : FakeAccounts.Platform.lemma_8a
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:11:20.846996+00:00
-- url     : https://prove2.me/theorems/df15a602-a908-4dca-ab1e-b6b2c1aea203
-- title:
--   Lemma 8(a), p. 8876 — No-pool case: costly separation at zero effort beats natural separation at d₂
-- statement:
--   Assume, in addition to the standing ranges, Assumption 3 of the paper, $p_0<\eta_2$. If $d_1\le 0$ (the pooling equilibrium is unavailable), then
--   $$\pi^{\text{csep}}_p(0)>\pi^{\text{nsep}}_p(d_2).$$
--
--   So when pooling is impossible the platform prefers zero effort, which induces costly separation, to the smallest effort that induces natural separation.
--
--   **Formalization Note** Assumption 3 (p. 8873) is used: it makes $d_2>0$. Without it $d_2\le 0$ and the comparison can fail.
-- source:
--   Huang and Liu, Economics of Social Media Fake Accounts, Management Science 71(10), 2025, p. 8876, Lemma 8(a); Assumption 3, p. 8873

import Mathlib
import Definitions.Def_FakeAccounts_Platform_Setting

namespace FakeAccounts.Platform

/-- Lemma 8(a), p. 8876 (under Assumption 3, p. 8873): if d₁ ≤ 0 then π_p^csep(0) > π_p^nsep(d₂). -/
theorem lemma_8a (P : Params) (hP : Standing P) (hA3 : P.p0 < eta2 P) :
    d1 P ≤ 0 → profit P .nsep (d2 P) < profit P .csep 0 := by sorry

end FakeAccounts.Platform
