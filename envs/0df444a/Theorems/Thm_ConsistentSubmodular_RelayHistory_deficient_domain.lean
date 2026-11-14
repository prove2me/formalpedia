-- Prove2me | Theorems.Thm_ConsistentSubmodular_RelayHistory_deficient_domain
-- name    : ConsistentSubmodular.RelayHistory.deficient_domain
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:34.917811+00:00
-- url     : https://prove2.me/theorems/d34ffbe0-e101-4db4-8504-b038d1a68b8d
-- title:
--   Parameter domain of a relay history at a deficient high stage
-- statement:
--   Let $P$ be a canonical atomic profile on stages $0,\dots,m$, with baseline $B_t$, residual $R(i,t)$, designated weight $A_t=R(t,t)$. Let $H$ be a relay history ending at stage $h$: it has a parent stage $\pi<h$, an active child $h$, a parameter $q\in[1,3)$, a high parent ($A_\pi>\tfrac34$) with access and strong credit, and the relay-edge conditions (envelope, positive denominator, $q$ equal to the raw ratio of $(\pi,h)$, safe edge, and the failure of the relevant eligibility test). Assume
--   $$A_h>\tfrac34,\qquad B_h<3\,(1-A_h).$$
--   Then all of the following hold:
--
--   1. $\tfrac43<q<2$;
--   2. $1-A_\pi<\tfrac18$;
--   3. $0\le \big(A_h-R(\pi,h)\big)-(q-1)\big(A_\pi-A_h\big)-3\,(1-A_\pi)$, i.e. the sufficient eligibility of the parent $\pi$ with parameter $q$ holds at the child $h$.
--
--   This describes the narrow region in which a relay into a high stage with small baseline (a deficient stage) can occur, and it feeds the middle-parent analysis of the deterministic certificate construction.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/MiddleParent.lean#L14-L67 (`ConsistentSubmodular.RelayHistory.deficient_domain`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SelectorState

open ConsistentSubmodular
open ConsistentSubmodular.RelayHistory
variable {m atomCount : ℕ} {P : AtomicProfile m atomCount} {h : Fin (m + 1)}

theorem ConsistentSubmodular.RelayHistory.deficient_domain (H : RelayHistory P h) (hP : P.Canonical)
    (hhigh : (3 : ℝ) / 4 < P.designated h)
    (hdef : P.baseline h < 3 * (1 - P.designated h)) :
    (4 : ℝ) / 3 < H.parameter ∧ H.parameter < 2 ∧
      1 - P.designated H.parent < 1 / 8 ∧
      0 ≤ P.suffEligibility H.parent H.parameter h := by sorry
