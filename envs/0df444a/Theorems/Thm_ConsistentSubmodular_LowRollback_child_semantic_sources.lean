-- Prove2me | Theorems.Thm_ConsistentSubmodular_LowRollback_child_semantic_sources
-- name    : ConsistentSubmodular.LowRollback.child_semantic_sources
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:07.309923+00:00
-- url     : https://prove2.me/theorems/56b3185b-bf3f-47c7-8b85-cbaadaf4d321
-- title:
--   Low rollback — the three child source inequalities at a failed attaining row
-- statement:
--   Throughout, $P$ is an atomic profile with stages $0,\dots,m$ (indexed by `Fin (m+1)`), with baseline $b_t$, residuals $r_{i,t}$, designated residual $d_t = r_{t,t}$ and benchmark $B_t = b_t + d_t$. $P$ is canonical: $d_0 = 1$ and $r_{i,t} \le d_t$ for all $i,t$. Write $\Delta_t = 1 - d_t$ (deficit) and $S_t = B_t - 1$ (shifted benchmark), and define the child quantities
--   $$T(q,d,p,\delta,P) = (3-q)P - q\delta - 4d - (4-q)p,\quad C(q,d,\delta,P) = (4-q)(1-d) - 4\delta - 4d - P,\quad I(q,d,P) = (4-q)^2 d - (q-2)^2 - qP.$$
--   Let $h \le s$ be stages, $q \le 4$ a real number with $d_h - r_{h,s} > 0$, and suppose the raw ratio $\rho(h,s)$ equals $q$. The actual eligibility is $E_h(q,t) = 4d_h - 3 - q(d_h - d_t) - \bigl(q - \tfrac{q^2}{4}\bigr) r_{h,t}$. Assume $E_h(q,s) \le 0$. Then, with $d = \Delta_h$, $p = S_h$, $\delta = \Delta_s - \Delta_h$ and $P = S_s$,
--
--   1. $0 \le T(q, \Delta_h, S_h, \Delta_s - \Delta_h, S_s)$,
--   2. $0 \le C(q, \Delta_h, \Delta_s - \Delta_h, S_s)$,
--   3. $0 \le I(q, \Delta_h, S_s)$.
--
--   This converts the profile-level hypotheses (an attaining row whose actual eligibility test fails) into the three scalar inequalities (persistence, capacity, ineligibility) that feed the scalar analysis of the low-parameter rollback case.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/LowRollbackSources.lean#L68-L88 (`ConsistentSubmodular.LowRollback.child_semantic_sources`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_LowRollbackSources

open ConsistentSubmodular
open ConsistentSubmodular.LowRollback
variable {m aCount : ℕ}

theorem ConsistentSubmodular.LowRollback.child_semantic_sources (P : AtomicProfile m aCount) (_hP : P.Canonical)
    (h s : Fin (m + 1)) (hhs : h ≤ s) (q : ℝ) (hq4 : q ≤ 4)
    (hden : 0 < P.designated h - P.residual h s) (hatt : P.rawRatio h s = q)
    (hno : P.actualEligibility h q s ≤ 0) :
    0 ≤ childPersistence q (deficit P h) (shifted P h)
      (deficit P s - deficit P h) (shifted P s) ∧
    0 ≤ childCapacity q (deficit P h) (deficit P s - deficit P h) (shifted P s) ∧
    0 ≤ childIneligibility q (deficit P h) (shifted P s) := by sorry
