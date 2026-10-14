-- Prove2me | Theorems.Thm_FakeAccounts_Platform_lemma_7
-- name    : FakeAccounts.Platform.lemma_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T04:10:42.177986+00:00
-- url     : https://prove2.me/theorems/71013698-edfc-441a-8b7b-3466721719b1
-- title:
--   Lemma 7, p. 8876 — within each equilibrium type the platform's profit strictly decreases in the antifake effort
-- statement:
--   For each equilibrium type $r\in\{\text{pool},\text{csep},\text{nsep}\}$, the platform's profit
--   $$\pi^r_p(d)=\lambda_p\mu E[n_r]-\frac{\gamma}{2}d^2$$
--   is strictly decreasing in the antifake effort $d$ on $[0,\infty)$.
--
--   Effort raises the consumers' following cost, lowering the number of real followers and so the advertising revenue, and it costs the platform $\frac{\gamma}{2}d^2$. This is the first ingredient of the platform's optimal-effort result.
--
--   **Formalization Note** The paper reads each $\pi^r_p$ only on the efforts that sustain equilibrium $r$; the statement holds on all of $d\ge 0$, which contains each of those ranges, so it is stated there.
-- source:
--   Huang and Liu, Economics of Social Media Fake Accounts, Management Science 71(10), 2025, p. 8876, Lemma 7

import Mathlib
import Definitions.Def_FakeAccounts_Platform_Setting

namespace FakeAccounts.Platform

/-- Lemma 7, p. 8876: π_p^pool, π_p^csep and π_p^nsep strictly decrease in d ≥ 0. -/
theorem lemma_7 (P : Params) (hP : Standing P) :
    ∀ r : Regime, StrictAntiOn (profit P r) (Set.Ici 0) := by sorry

end FakeAccounts.Platform
