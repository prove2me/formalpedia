-- Prove2me | Theorems.Thm_ConsistentSubmodular_LowRollback_attainer_credit_exceeds
-- name    : ConsistentSubmodular.LowRollback.attainer_credit_exceeds
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:26.322338+00:00
-- url     : https://prove2.me/theorems/a83799d6-8de6-49e9-86f8-13408cd2834e
-- title:
--   Low rollback — the child attainer lies above the parent's credit ceiling
-- statement:
--   Define
--   $$F(k,d_0,d,p) = (3-k)p - kd - 2(4-k)d_0,\quad T(q,d,p,\delta,P) = (3-q)P - q\delta - 4d - (4-q)p,\quad \bar p(k,d_0) = 2 - \frac{3}{k} + \frac{3(4-k)d_0}{k}.$$
--   Let $k,q,d_0,d,p,\delta,P$ be real numbers with $\tfrac{40}{23} < k < 3$, $q \ge 0$, $d \ge \tfrac16$, $d_0 \ge 0$, $\delta \ge 0$ and $p \le P$. If $F(k,d_0,d,p) \ge 0$ and $T(q,d,p,\delta,P) \ge 0$, then
--   $$\bar p(k,d_0) < P.$$
--   In words, the child attainer's shifted benchmark $P$ lies strictly beyond the whole eligible-credit ceiling $\bar p(k,d_0)$ of the failed parent. It supplies the chronology input for the rollback argument in the low-parameter case of the deterministic checkpoint construction.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/LowRollbackSources.lean#L125-L154 (`ConsistentSubmodular.LowRollback.attainer_credit_exceeds`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackSources

open ConsistentSubmodular
open ConsistentSubmodular.LowRollback
variable {m aCount : ℕ}

theorem ConsistentSubmodular.LowRollback.attainer_credit_exceeds (k q d₀ d p δ P : ℝ)
    (hk : 40 / 23 < k) (hk3 : k < 3) (hq : 0 ≤ q)
    (hd : 1 / 6 ≤ d) (hd₀ : 0 ≤ d₀) (hδ : 0 ≤ δ) (hPp : p ≤ P)
    (hI : 0 ≤ parentFloor k d₀ d p)
    (hF : 0 ≤ childPersistence q d p δ P) : ceiling k d₀ < P := by sorry
