-- Prove2me | Theorems.Thm_ConsistentSubmodular_LowRollback_SJ_positive
-- name    : ConsistentSubmodular.LowRollback.SJ_positive
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:09.870256+00:00
-- url     : https://prove2.me/theorems/53df5991-efa1-42f9-909c-0a4e0bf4b4c3
-- title:
--   Low rollback — the discriminant polynomial $S_J$ is positive whenever $S_L$ is
-- statement:
--   Let $c(q) = (3-q)(4-q)^2 - 4q$, $n(q) = (3-q)(q-2)^2$, $a(q) = q(4-q)$ and put
--   $$S_A = n + 2c + 2a,\; S_B = 9c + 3a,\; S_D = 4c + 3a,\; S_E = 5c + 3a,$$
--   $$S_\beta(k,q) = (9-4k)c - 3k a,\quad S_L(k,q) = S_\beta(k,q) - kc,$$
--   all evaluated at $q$. Define
--   $$S_J(k,q) = (S_E^2 - 4S_DS_A)k^2 + (36cS_A + 4S_DS_B - 18cS_E - 4S_E^2)k - 27c^2.$$
--   If $k \ge \tfrac43$, $0 \le q \le 1$ and $S_L(k,q) > 0$, then $S_J(k,q) > 0$.
--
--   This is a purely algebraic step of the low-rollback source-exclusion analysis: positivity of the linear form $S_L$ forces positivity of the quadratic form $S_J$ on the relevant parameter range.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/LowRollbackExclusions.lean#L102-L153 (`ConsistentSubmodular.LowRollback.SJ_positive`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackExclusions

set_option maxHeartbeats 1500000
open ConsistentSubmodular ConsistentSubmodular.LowRollback

theorem ConsistentSubmodular.LowRollback.SJ_positive (k q : ℝ) (hk : 4 / 3 ≤ k)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (hL : 0 < SL k q) : 0 < SJ k q := by sorry
