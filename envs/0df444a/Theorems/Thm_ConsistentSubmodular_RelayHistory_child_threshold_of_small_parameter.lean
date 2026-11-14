-- Prove2me | Theorems.Thm_ConsistentSubmodular_RelayHistory_child_threshold_of_small_parameter
-- name    : ConsistentSubmodular.RelayHistory.child_threshold_of_small_parameter
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:08.214124+00:00
-- url     : https://prove2.me/theorems/8b26f600-567f-4d31-b58a-8da55d731bc7
-- title:
--   A small relay parameter forces the child above the threshold anchor
-- statement:
--   Throughout, $P$ is an atomic profile with stages $0,\dots,m$ (indexed by `Fin (m+1)`), with baseline $b_t$, residuals $r_{i,t}$, designated residual $d_t = r_{t,t}$ and benchmark $B_t = b_t + d_t$. $P$ is canonical: $d_0 = 1$ and $r_{i,t} \le d_t$ for all $i,t$. Let $h$ be a stage and let $H$ be a relay history of $P$ ending at child $h$ (a parent stage $a < h$ with a $\tfrac34$-safe access, strong credit, an attaining row with parameter $k \in [1,3)$, a safe edge from $a$ to $h$, and failed eligibility tests). If the history parameter satisfies $k < \tfrac43$, then
--   $$d_h > \tfrac{1281}{1600}.$$
--   That is, short relays only reach children whose designated residual is above the threshold anchor, so the low rollback regime ($d_h < \tfrac{1281}{1600}$) occurs only for histories with parameter at least $\tfrac43$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/ProfileEligibility.lean#L106-L122 (`ConsistentSubmodular.RelayHistory.child_threshold_of_small_parameter`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SelectorState

open ConsistentSubmodular
open ConsistentSubmodular.RelayHistory
variable {m atomCount : ℕ} {P : AtomicProfile m atomCount} {h : Fin (m + 1)}

theorem ConsistentSubmodular.RelayHistory.child_threshold_of_small_parameter (H : RelayHistory P h) (hP : P.Canonical)
    (hk : H.parameter < 4 / 3) : (1281 : ℝ) / 1600 < P.designated h := by sorry
