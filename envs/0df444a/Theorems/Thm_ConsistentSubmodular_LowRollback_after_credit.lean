-- Prove2me | Theorems.Thm_ConsistentSubmodular_LowRollback_after_credit
-- name    : ConsistentSubmodular.LowRollback.after_credit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:23.776703+00:00
-- url     : https://prove2.me/theorems/54ba5ce4-1779-4f82-9a3f-dc33c4940b9a
-- title:
--   Low rollback — positivity of the credit $Y$ after the rollback point
-- statement:
--   Define
--   $$F(k,d_0,d,p) = (3-k)p - kd - 2(4-k)d_0,\quad \bar p(k,d_0) = 2-\tfrac3k+\tfrac{3(4-k)d_0}{k},$$
--   $$T(q,d,p,\delta,P) = (3-q)P - q\delta - 4d - (4-q)p,\quad C(q,d,\delta,P) = (4-q)(1-d) - 4\delta - 4d - P,\quad I(q,d,P) = (4-q)^2d - (q-2)^2 - qP,$$
--   $$Y(k,d_0,d,p,\delta,P) = \tfrac{(k-1)(3-k)}{k}\bigl(P - (k-1)(d+\delta) - (4-k)d_0\bigr) + \tfrac{k^2-3k+3}{k}\,p - \bar p(k,d_0).$$
--   Let $k,q,d_0,d,p,\delta,P$ be reals with $\tfrac{40}{23} < k < \tfrac{40}{17}$, $0 < q \le 1$, $d_0 \ge 0$, $\delta \ge 0$ and $20 - 11k + (2k-5)q < 0$. If
--   $$F(k,d_0,d,p) \ge 0,\quad T(q,d,p,\delta,P) \ge 0,\quad C(q,d,\delta,P) \ge 0,\quad I(q,d,P) \ge 0,$$
--   then $Y(k,d_0,d,p,\delta,P) > 0$.
--
--   This is the final credit estimate for the stages after the rollback point, combining the parent floor with the three child source inequalities.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/LowRollbackAfter.lean#L103-L251 (`ConsistentSubmodular.LowRollback.after_credit`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackSources

set_option maxHeartbeats 2000000
open ConsistentSubmodular ConsistentSubmodular.LowRollback

theorem ConsistentSubmodular.LowRollback.after_credit (k q d₀ d p δ P : ℝ)
    (hk0 : 40 / 23 < k) (hk1 : k < 40 / 17) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hH : 20 - 11 * k + (2 * k - 5) * q < 0) (hd₀ : 0 ≤ d₀) (hδ : 0 ≤ δ)
    (hF : 0 ≤ parentFloor k d₀ d p)
    (hT : 0 ≤ childPersistence q d p δ P)
    (hC : 0 ≤ childCapacity q d δ P)
    (hE : 0 ≤ childIneligibility q d P) : 0 < Y k d₀ d p δ P := by sorry
