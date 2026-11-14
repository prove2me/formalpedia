-- Prove2me | Theorems.Thm_ConsistentSubmodular_LowRollback_remainder_positive
-- name    : ConsistentSubmodular.LowRollback.remainder_positive
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:40.38119+00:00
-- url     : https://prove2.me/theorems/836ecf82-e381-4b67-b314-dcdfa827de21
-- title:
--   Low rollback — positivity of the remainder polynomial on $[-\tfrac12,\tfrac12]\times[0,1]$
-- statement:
--   Define
--   $$R(x,q) = -(3-q)(2-q)^2x^4 + 3(q-2)^2x^3 + (2-q)(5q^2 - 25q + 54)x^2 - 3(q^3 - 3q^2 - 4q + 4)x - 2q^3 + 14q^2 - 20q + 12.$$
--   For all real $x$ and $q$ with $-\tfrac12 \le x \le \tfrac12$ and $0 \le q \le 1$,
--   $$R(x,q) > 0.$$
--   This is a two-variable polynomial positivity bound used in the numerical certificate for the stages after the rollback point in the low-parameter case.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/LowRollbackAfter.lean#L51-L101 (`ConsistentSubmodular.LowRollback.remainder_positive`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackAfter

set_option maxHeartbeats 2000000
open ConsistentSubmodular ConsistentSubmodular.LowRollback

theorem ConsistentSubmodular.LowRollback.remainder_positive (x q : ℝ) (hx0 : -(1 / 2) ≤ x) (hx1 : x ≤ 1 / 2)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : 0 < remainder x q := by sorry
