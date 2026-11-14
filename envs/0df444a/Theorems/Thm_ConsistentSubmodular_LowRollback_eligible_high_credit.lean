-- Prove2me | Theorems.Thm_ConsistentSubmodular_LowRollback_eligible_high_credit
-- name    : ConsistentSubmodular.LowRollback.eligible_high_credit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:22.509496+00:00
-- url     : https://prove2.me/theorems/358afc9f-81d1-4b6f-8cf4-aa1f3aa103e8
-- title:
--   Low rollback — positivity of the eligible credit $U$ for $k \ge 20/11$
-- statement:
--   Let $\bar p(k,d_0) = 2 - \frac3k + \frac{3(4-k)d_0}{k}$, $U(k,d_0,d,p,W) = d - 2\bar p(k,d_0) + 3p - (3-k)W$, and $c(q) = (3-q)(4-q)^2 - 4q$, $n(q) = (3-q)(q-2)^2$, $a(q) = q(4-q)$. Let $k,q,d_0,d,p,W$ be real numbers with $\tfrac{20}{11} \le k < 3$, $0 < q \le 1$, $0 \le d_0 \le d$ and $\tfrac{319}{1600} \le d \le \tfrac14$. Assume
--
--   1. (attainment) $p = (4-k)W - kd - (4-k)d_0$,
--   2. $W + d_0 \le p$ and $p \le \bar p(k,d_0)$,
--   3. (child row) $0 \le c(q)\,d - n(q) - a(q)\,p$.
--
--   Then $U(k,d_0,d,p,W) > 0$.
--
--   This is the high-parameter analogue of the eligible-credit estimate, completing the exclusion of eligible target rows in the low rollback.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/LowRollbackEligibleHigh.lean#L58-L115 (`ConsistentSubmodular.LowRollback.eligible_high_credit`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackSources

open ConsistentSubmodular ConsistentSubmodular.LowRollback

theorem ConsistentSubmodular.LowRollback.eligible_high_credit (k q d₀ d p W : ℝ)
    (hk : 20 / 11 ≤ k) (hk3 : k < 3) (hq : 0 < q) (hq1 : q ≤ 1)
    (hd₀ : 0 ≤ d₀) (hd₀d : d₀ ≤ d) (hd : 319 / 1600 ≤ d) (hd4 : d ≤ 1 / 4)
    (hatt : p = (4 - k) * W - k * d - (4 - k) * d₀)
    (hpW : W + d₀ ≤ p) (hpC : p ≤ ceiling k d₀)
    (hchild : 0 ≤ cpoly q * d - npoly q - apoly q * p) :
    0 < U k d₀ d p W := by sorry
