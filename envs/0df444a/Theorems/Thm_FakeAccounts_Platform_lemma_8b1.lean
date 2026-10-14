-- Prove2me | Theorems.Thm_FakeAccounts_Platform_lemma_8b1
-- name    : FakeAccounts.Platform.lemma_8b1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:11:16.182792+00:00
-- url     : https://prove2.me/theorems/e03efdf2-5bcb-49c4-89ba-3b9aa289b768
-- title:
--   Lemma 8(b)(1), p. 8876 — All-eqm case: pooling at zero effort beats costly separation at d₁
-- statement:
--   If $d_1>0$ (all three equilibria are available), then
--   $$\pi^{\text{pool}}_p(0)>\pi^{\text{csep}}_p(d_1).$$
--
--   Pooling at zero effort earns more advertising revenue than separation and carries no effort cost.
-- source:
--   Huang and Liu, Economics of Social Media Fake Accounts, Management Science 71(10), 2025, p. 8876, Lemma 8(b)(1)

import Mathlib
import Definitions.Def_FakeAccounts_Platform_Setting

namespace FakeAccounts.Platform

/-- Lemma 8(b)(1), p. 8876: if d₁ > 0 then π_p^pool(0) > π_p^csep(d₁). -/
theorem lemma_8b1 (P : Params) (hP : Standing P) :
    0 < d1 P → profit P .csep (d1 P) < profit P .pool 0 := by sorry

end FakeAccounts.Platform
