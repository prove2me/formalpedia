-- Prove2me | Theorems.Thm_ConsistentSubmodular_AtomicProfile_selector_step
-- name    : ConsistentSubmodular.AtomicProfile.selector_step
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:36.08863+00:00
-- url     : https://prove2.me/theorems/5aee2671-7ea9-428b-8cab-7a83b8e8c208
-- title:
--   Selector step — a certificate or a strictly later selector state
-- statement:
--   Let $P$ be a canonical atomic profile on stages $0,\dots,m$, let $h$ be a stage, and let $S$ be a selector state at $h$ (anchor with $\tfrac34<A_h<1$, an access certificate and strong credit at $h$, and a relay history). Then at least one of the following holds:
--
--   1. there is a checkpoint certificate for $P$ (a point of the simplex with support of size at most $2$ and value at least $\tfrac34P_t$ at every stage $t$, together with a safe entry path from $\delta_0$ and a safe exit path to $\delta_m$, with at most $m+3$ pieces in total);
--   2. there is a stage $s>h$ carrying a selector state.
--
--   This is the complete decision of the selector at one stage: either the procedure terminates with a certificate, or it relays to a strictly later stage while keeping all invariants. Iterating it over the finitely many stages (the index strictly increases, so the iteration stops) gives the finite checkpoint statement.
--
--   **Formalization Note**: both alternatives are stated as `Nonempty` of the respective data type (certificate or selector state).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/FiniteCheckpoint.lean#L16-L37 (`ConsistentSubmodular.AtomicProfile.selector_step`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SelectorState

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem ConsistentSubmodular.AtomicProfile.selector_step (hP : P.Canonical) (h : Fin (m + 1)) (S : SelectorState P h) :
    Nonempty (CheckpointCertificate P) ∨ ∃ s, h < s ∧ Nonempty (SelectorState P s) := by sorry
