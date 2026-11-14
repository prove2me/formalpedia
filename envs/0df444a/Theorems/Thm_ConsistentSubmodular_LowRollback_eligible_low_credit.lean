-- Prove2me | Theorems.Thm_ConsistentSubmodular_LowRollback_eligible_low_credit
-- name    : ConsistentSubmodular.LowRollback.eligible_low_credit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:53.397282+00:00
-- url     : https://prove2.me/theorems/92f902a6-f2b6-4cf3-947b-92ecf94b1237
-- title:
--   Low rollback — positivity of the eligible credit $U$ for $k \le 20/11$
-- statement:
--   Let $\bar p(k,d_0) = 2 - \frac3k + \frac{3(4-k)d_0}{k}$ and
--   $$U(k,d_0,d,p,W) = d - 2\bar p(k,d_0) + 3p - (3-k)W.$$
--   Let $k,d_0,d,p,W$ be real numbers with $\tfrac{40}{23} \le k \le \tfrac{20}{11}$, $d \ge \tfrac{319}{1600}$ and $0 \le d_0 \le d$. Assume
--
--   1. (attainment) $p = (4-k)W - kd - (4-k)d_0$,
--   2. (weak credit) $W + d_0 \le p$.
--
--   Then $U(k,d_0,d,p,W) > 0$.
--
--   This is the low-parameter eligible-credit estimate, used to rule out an eligible target row in the low rollback case.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/LowRollbackEligible.lean#L39-L79 (`ConsistentSubmodular.LowRollback.eligible_low_credit`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackTargets

open ConsistentSubmodular ConsistentSubmodular.LowRollback

theorem ConsistentSubmodular.LowRollback.eligible_low_credit (k d₀ d p W : ℝ)
    (hk0 : 40 / 23 ≤ k) (hk1 : k ≤ 20 / 11)
    (hd : 319 / 1600 ≤ d) (hd₀ : 0 ≤ d₀) (hd₀d : d₀ ≤ d)
    (hatt : p = (4 - k) * W - k * d - (4 - k) * d₀) (hweak : W + d₀ ≤ p) :
    0 < U k d₀ d p W := by sorry
