-- Prove2me | Theorems.Thm_ConsistentSubmodular_LowRollback_before_high_credit
-- name    : ConsistentSubmodular.LowRollback.before_high_credit
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:57.896789+00:00
-- url     : https://prove2.me/theorems/7510d0d0-ebba-42c3-9751-4db06c45929e
-- title:
--   Low rollback — positivity of the credit $V_{\mathrm{high}}$ before the rollback point
-- statement:
--   Let $F(k,d_0,d,p) = (3-k)p - kd - 2(4-k)d_0$, $d_q(q) = q^2-3q+3$, $c(q) = (3-q)(4-q)^2 - 4q$, $n(q) = (3-q)(q-2)^2$, $a(q) = q(4-q)$, and
--   $$V_{\mathrm{high}}(k,d_0,d,p,\delta) = p - (k-2) - (k-1)(3-k)(d+\delta) - (4-k)^2 d_0.$$
--   Let $k,q,d_0,d,p,\delta$ be real numbers with $2 \le k < 3$, $0 < q \le 1$, $d > 0$, $d_0 \ge 0$, $\delta \ge 0$. Assume
--
--   1. $F(k,d_0,d,p) \ge 0$,
--   2. $0 \le (5-3q)d - p - d_q(q)\,\delta$,
--   3. $0 \le c(q)\,d - n(q) - a(q)\,p - q^2\delta$.
--
--   Then $V_{\mathrm{high}}(k,d_0,d,p,\delta) > 0$.
--
--   This is the counterpart of the low-credit estimate for the high parameter range $k \ge 2$, used in the same rollback analysis.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/LowRollbackBeforeHigh.lean#L58-L140 (`ConsistentSubmodular.LowRollback.before_high_credit`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackSources

open ConsistentSubmodular ConsistentSubmodular.LowRollback

theorem ConsistentSubmodular.LowRollback.before_high_credit (k q d₀ d p δ : ℝ)
    (hk2 : 2 ≤ k) (hk3 : k < 3) (hq0 : 0 < q) (hq1 : q ≤ 1)
    (hd : 0 < d) (hd₀ : 0 ≤ d₀) (hδ : 0 ≤ δ)
    (hI : 0 ≤ parentFloor k d₀ d p)
    (hR : 0 ≤ (5 - 3 * q) * d - p - dpoly q * δ)
    (hJ : 0 ≤ cpoly q * d - npoly q - apoly q * p - q ^ 2 * δ) :
    0 < VHigh k d₀ d p δ := by sorry
