-- Prove2me | Theorems.Thm_ConsistentSubmodular_LowRollback_before_low_credit
-- name    : ConsistentSubmodular.LowRollback.before_low_credit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:51.417898+00:00
-- url     : https://prove2.me/theorems/39f91163-509b-43b5-967c-e1524b1e35bd
-- title:
--   Low rollback — positivity of the credit $V$ before the rollback point
-- statement:
--   Let $F(k,d_0,d,p) = (3-k)p - kd - 2(4-k)d_0$, $d_q(q) = q^2 - 3q + 3$ and
--   $$V(k,d_0,d,p,\delta) = p + (3-2k)(d+\delta) - 2(4-k)d_0.$$
--   Let $k,q,d_0,d,p,\delta$ be real numbers with $k < 3$, $0 < q \le 1$, $d > 0$, $d_0 \ge 0$ and $20 - 11k + (2k-5)q < 0$. Assume
--
--   1. $F(k,d_0,d,p) \ge 0$,
--   2. $0 \le (5-3q)d - p - d_q(q)\,\delta$.
--
--   Then $V(k,d_0,d,p,\delta) > 0$.
--
--   This is the low-credit estimate for stages before the rollback point in the low-parameter case of the deterministic checkpoint construction.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/LowRollbackBefore.lean#L10-L58 (`ConsistentSubmodular.LowRollback.before_low_credit`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackSources

open ConsistentSubmodular ConsistentSubmodular.LowRollback

theorem ConsistentSubmodular.LowRollback.before_low_credit (k q d₀ d p δ : ℝ)
    (hk3 : k < 3) (hq0 : 0 < q) (hq1 : q ≤ 1) (hd : 0 < d) (hd₀ : 0 ≤ d₀)
    (hH : 20 - 11 * k + (2 * k - 5) * q < 0)
    (hI : 0 ≤ parentFloor k d₀ d p)
    (hR : 0 ≤ (5 - 3 * q) * d - p - dpoly q * δ) : 0 < V k d₀ d p δ := by sorry
