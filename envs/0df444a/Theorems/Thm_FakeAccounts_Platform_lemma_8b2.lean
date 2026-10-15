-- Prove2me | Theorems.Thm_FakeAccounts_Platform_lemma_8b2
-- name    : FakeAccounts.Platform.lemma_8b2
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-14T04:11:10.384997+00:00
-- url     : https://prove2.me/theorems/d250dbf4-7415-4e20-a612-4c535b96128e
-- title:
--   Lemma 8(b)(2), p. 8876 — All-eqm case: costly separation at d₁ beats natural separation at d₂
-- statement:
--   If $d_1>0$, then
--   $$\pi^{\text{csep}}_p(d_1)>\pi^{\text{nsep}}_p(d_2).$$
--
--   The two separating equilibria reveal the same information, but natural separation requires the higher effort $d_2>d_1$.
-- source:
--   Huang and Liu, Economics of Social Media Fake Accounts, Management Science 71(10), 2025, p. 8876, Lemma 8(b)(2)

import Mathlib
import Definitions.Def_FakeAccounts_Platform_Setting

namespace FakeAccounts.Platform

/-- Lemma 8(b)(2), p. 8876: if d₁ > 0 then π_p^csep(d₁) > π_p^nsep(d₂). -/
theorem lemma_8b2 (P : Params) (hP : Standing P) :
    0 < d1 P → profit P .nsep (d2 P) < profit P .csep (d1 P) := by sorry

end FakeAccounts.Platform
