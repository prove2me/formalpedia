-- Prove2me | Theorems.Thm_ConsistentSubmodular_LowRollback_child_coefficients
-- name    : ConsistentSubmodular.LowRollback.child_coefficients
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:41.637749+00:00
-- url     : https://prove2.me/theorems/b370e74e-626d-4344-b172-121baa939db9
-- title:
--   Low rollback — sign and size bounds for the child coefficient polynomials
-- statement:
--   Define the polynomials
--   $$c(q) = (3-q)(4-q)^2 - 4q,\quad n(q) = (3-q)(q-2)^2,\quad a(q) = q(4-q),$$
--   and $S_A(q) = n(q) + 2c(q) + 2a(q)$. For every real $q$ with $0 \le q \le 1$:
--
--   1. $c(q) \ge 14$,
--   2. $a(q) \ge 0$,
--   3. $a(q) \le 3$,
--   4. $S_A(q) > 0$.
--
--   These elementary bounds on the coefficients of the child inequalities are the scalar inputs for the polynomial sign analysis in the low-parameter rollback case.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/LowRollbackExclusions.lean#L25-L41 (`ConsistentSubmodular.LowRollback.child_coefficients`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackExclusions

set_option maxHeartbeats 1500000
open ConsistentSubmodular ConsistentSubmodular.LowRollback

theorem ConsistentSubmodular.LowRollback.child_coefficients (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    14 ≤ cpoly q ∧ 0 ≤ apoly q ∧ apoly q ≤ 3 ∧ 0 < SA q := by sorry
