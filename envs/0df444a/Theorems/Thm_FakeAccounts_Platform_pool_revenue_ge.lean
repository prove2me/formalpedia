-- Prove2me | Theorems.Thm_FakeAccounts_Platform_pool_revenue_ge
-- name    : FakeAccounts.Platform.pool_revenue_ge
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:11:03.636916+00:00
-- url     : https://prove2.me/theorems/ab17ecd2-e1d1-4744-a6d4-f57c0495efdd
-- title:
--   p. 8876, discussion of Lemma 8(b.1) — expected real followers, hence advertising revenue, are higher under pooling
-- statement:
--   For every antifake effort $d\ge 0$, the expected number of real followers paid for, $E[n_r]$ computed from (10)–(12), is at least as large under the pooling equilibrium as under the costly separating equilibrium, and strictly larger when the following cost $c=c_0+c_1(1-\tau)d$ is positive:
--   $$E[n^{\text{csep}}_r](d)\le E[n^{\text{pool}}_r](d),\qquad c>0\implies E[n^{\text{csep}}_r](d)<E[n^{\text{pool}}_r](d).$$
--   Since the advertising revenue is $\mu E[n_r]$ and the platform's share is $\lambda_p\mu E[n_r]$, both are higher under pooling.
--
--   **Formalization Note** The paper says "higher"; the weak inequality covers $c=0$ (possible at $d=0$ when $c_0=0$), where the two coincide, and the strict one holds whenever $c>0$.
-- source:
--   Huang and Liu, Economics of Social Media Fake Accounts, Management Science 71(10), 2025, p. 8876, paragraph after Lemma 8 ("Therefore, the advertising revenue … is higher under a pooling equilibrium")

import Mathlib
import Definitions.Def_FakeAccounts_Platform_Setting

namespace FakeAccounts.Platform

/-- p. 8876, discussion of Lemma 8(b.1): the expected number of real followers, hence the
advertising revenue, is higher under pooling than under costly separation (strictly when c > 0). -/
theorem pool_revenue_ge (P : Params) (hP : Standing P) :
    ∀ d, 0 ≤ d → expReal P .csep d ≤ expReal P .pool d ∧
      (0 < cost P d → expReal P .csep d < expReal P .pool d) := by sorry

end FakeAccounts.Platform
