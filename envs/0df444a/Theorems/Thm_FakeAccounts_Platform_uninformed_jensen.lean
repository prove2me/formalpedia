-- Prove2me | Theorems.Thm_FakeAccounts_Platform_uninformed_jensen
-- name    : FakeAccounts.Platform.uninformed_jensen
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:41.822049+00:00
-- url     : https://prove2.me/theorems/9c329e56-d5eb-4a9a-8b28-ddfc0ff1d07d
-- title:
--   p. 8876, discussion of Lemma 8(b.1) — uninformed followers at mean quality exceed the average over an H- and an L-type
-- statement:
--   Let $n_{un}(\bar q)=(1-l)(1-c/\bar q)$ be the number of uninformed followers when the expected quality given the signal is $\bar q$, and $E[q]=\rho q_H+(1-\rho)q_L$. For every effort $d$ whose following cost $c=c_0+c_1(1-\tau)d$ is positive,
--   $$\rho\,n_{un}(q_H)+(1-\rho)\,n_{un}(q_L)\;<\;n_{un}(E[q]).$$
--   The left side is the expected number of uninformed followers under a separating equilibrium, the right side the number under pooling.
--
--   This is the concavity comparison the paper uses to explain why pooling yields more advertising revenue.
--
--   **Formalization Note** The hypothesis $c>0$ is added: with $c=0$ every uninformed consumer follows and both sides equal $1-l$, so the page's strict "higher" needs it. The "average" is the $\rho$-weighted one, as in (11).
-- source:
--   Huang and Liu, Economics of Social Media Fake Accounts, Management Science 71(10), 2025, p. 8876, paragraph after Lemma 8 ("To see Lemma 8(b.1) …")

import Mathlib
import Definitions.Def_FakeAccounts_Platform_Setting

namespace FakeAccounts.Platform

/-- p. 8876, discussion of Lemma 8(b.1): with a positive following cost, uninformed followers of
an influencer of mean quality exceed the ρ-weighted average of those of an H- and an L-type. -/
theorem uninformed_jensen (P : Params) (hP : Standing P) :
    ∀ d, 0 < cost P d →
      P.rho * nUn P P.qH d + (1 - P.rho) * nUn P P.qL d < nUn P (meanQ P) d := by sorry

end FakeAccounts.Platform
