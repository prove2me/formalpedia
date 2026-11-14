-- Prove2me | Theorems.Thm_ConsistentSubmodular_AtomicProfile_root_checkpoint_or_state
-- name    : ConsistentSubmodular.AtomicProfile.root_checkpoint_or_state
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:20:49.646041+00:00
-- url     : https://prove2.me/theorems/5c0f73f5-6e89-4e76-a255-0f0d70e47dbd
-- title:
--   Root initialization: a checkpoint certificate or a selector state
-- statement:
--   Let $P$ be a canonical atomic profile on stages $0,\dots,m$ whose designated weights satisfy $A_t<1$ for every stage $t>0$. Then
--   $$\text{a checkpoint certificate for } P \text{ exists}\quad\text{or}\quad \exists\, h \text{ such that a selector state at } h \text{ exists.}$$
--
--   Here a checkpoint certificate is a point of the simplex of support size at most $2$ with value at least $\tfrac34\beta_t$ at every stage $t$ (where $\beta_t$ is the benchmark), together with safe entry and exit polygonal paths using at most $(m+1)+2$ affine pieces in total. A selector state at $h$ consists of $\tfrac34<A_h<1$, an access certificate, strong credit at $h$ and a relay history ending at $h$.
--
--   The result initializes the selector argument: from the root stage one either directly obtains a checkpoint or enters the relay process with a first selector state. The root initialization includes an additional actual-credit test below parameter two, so that every returned relay state retains the failure condition needed for rollback.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Certificates/RootInitialization.lean#L19-L154 (`ConsistentSubmodular.AtomicProfile.root_checkpoint_or_state`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Certificates_SelectorState

open ConsistentSubmodular
open ConsistentSubmodular.AtomicProfile
variable {m atomCount : ℕ} (P : AtomicProfile m atomCount)

theorem ConsistentSubmodular.AtomicProfile.root_checkpoint_or_state (hP : P.Canonical)
    (hstrict : ∀ t : Fin (m + 1), 0 < t → P.designated t < 1) :
    Nonempty (CheckpointCertificate P) ∨ ∃ h, Nonempty (SelectorState P h) := by sorry
