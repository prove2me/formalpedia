-- Prove2me | Theorems.Thm_ConsistentSubmodular_LowRollback_source_exclusions
-- name    : ConsistentSubmodular.LowRollback.source_exclusions
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:41.497198+00:00
-- url     : https://prove2.me/theorems/4d9bbca5-f757-40f0-b8bf-396b0cbe0d5f
-- title:
--   Low rollback — exclusion of the forbidden source regions
-- statement:
--   Let $c(q) = (3-q)(4-q)^2 - 4q$, $n(q) = (3-q)(q-2)^2$, $a(q) = q(4-q)$. Let $k,q,d_0,d,p,p_a$ be real numbers with
--   $$\tfrac43 \le k \le \tfrac{20}{11},\quad 0 \le q \le 1,\quad p_a \ge 0,\quad 0 \le d_0 \le \tfrac14,$$
--   and assume
--
--   1. (strong credit) $p_a \ge \tfrac12$ or $d_0 \le p_a(1-p_a)$,
--   2. (parent) $0 \le (3-k)p - kd - (4-k)(d_0 + p_a)$,
--   3. (failed credit) $0 \le 2k - 3 + 3(4-k)d_0 - kp$,
--   4. (child row) $0 \le c(q)\,d - n(q) - a(q)\,p$.
--
--   Then
--   $$\tfrac{40}{23} < k \quad\text{and}\quad 20 - 11k + (2k-5)q < 0.$$
--   Thus both forbidden source regions are excluded: exact parent strong credit, failed credit and the eliminated child attaining-row floor cannot hold together unless the parameter lies above $\tfrac{40}{23}$ and the linear threshold inequality in $(k,q)$ holds. This is the numerical core of the source analysis in the low-parameter rollback.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/LowRollbackExclusions.lean#L155-L233 (`ConsistentSubmodular.LowRollback.source_exclusions`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackSources

set_option maxHeartbeats 1500000
open ConsistentSubmodular ConsistentSubmodular.LowRollback

theorem ConsistentSubmodular.LowRollback.source_exclusions (k q d₀ d p pa : ℝ)
    (hk0 : 4 / 3 ≤ k) (hk1 : k ≤ 20 / 11) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hpa : 0 ≤ pa) (_hd₀ : 0 ≤ d₀) (hd₀hi : d₀ ≤ 1 / 4)
    (hstrong : 1 / 2 ≤ pa ∨ d₀ ≤ pa * (1 - pa))
    (hparent : 0 ≤ (3 - k) * p - k * d - (4 - k) * (d₀ + pa))
    (hcredit : 0 ≤ 2 * k - 3 + 3 * (4 - k) * d₀ - k * p)
    (hchild : 0 ≤ cpoly q * d - npoly q - apoly q * p) :
    40 / 23 < k ∧ 20 - 11 * k + (2 * k - 5) * q < 0 := by sorry
