-- Prove2me | Theorems.Thm_ConsistentSubmodular_LowRollback_source_parameter_upper
-- name    : ConsistentSubmodular.LowRollback.source_parameter_upper
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:21.78943+00:00
-- url     : https://prove2.me/theorems/83f6ef7c-335a-4b17-a5b2-6986e32b821b
-- title:
--   Low rollback — upper bound $k < 40/17$ on the source parameter
-- statement:
--   Let $F(k,d_0,d,p) = (3-k)p - kd - 2(4-k)d_0$ and $\bar p(k,d_0) = 2 - \frac3k + \frac{3(4-k)d_0}{k}$. Let $k,d_0,d,p$ be real numbers with $\tfrac43 \le k < 3$, $d \ge \tfrac{319}{1600}$ and $d_0 \ge 0$. If $F(k,d_0,d,p) \ge 0$ and $p < \bar p(k,d_0)$, then
--   $$k < \tfrac{40}{17}.$$
--   Together with the lower bound on $k$ obtained from the source exclusions, this confines the parameter of a failed source row to a bounded window, which is needed for the later numerical cases of the low rollback.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/LowRollbackExclusions.lean#L235-L255 (`ConsistentSubmodular.LowRollback.source_parameter_upper`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackSources

set_option maxHeartbeats 1500000
open ConsistentSubmodular ConsistentSubmodular.LowRollback

theorem ConsistentSubmodular.LowRollback.source_parameter_upper (k d₀ d p : ℝ)
    (hk0 : 4 / 3 ≤ k) (hk3 : k < 3) (hd : 319 / 1600 ≤ d) (hd₀ : 0 ≤ d₀)
    (hI : 0 ≤ parentFloor k d₀ d p) (hp : p < ceiling k d₀) : k < 40 / 17 := by sorry
