-- Prove2me | Theorems.Thm_ConsistentSubmodular_ProtectedPrograms_arrived_bound
-- name    : ConsistentSubmodular.ProtectedPrograms.arrived_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:39.624631+00:00
-- url     : https://prove2.me/theorems/1763a0a8-2fbb-4a81-a8cf-ea805e118f9f
-- title:
--   Selected set at time $t$ consists of arrived elements
-- statement:
--   Let $f$ be an objective on $[n]$, $C$ a protected clock, and $P$ a family of protected programs for $(f,\kappa,\beta,C,R,B)$. Then for every time $t\in\mathbb N$ the selected set satisfies
--   $$P.\mathrm{selected}(t)\subseteq X_t,$$
--   where $X_t=\{e\in[n]: e<t\}$ is the prefix of the first $t$ arrivals. Here $P.\mathrm{selected}(t)$ is the union of the core $P.\mathrm{core}(t)$ (the trajectory obtained by following the program paths block by block along the clock) and the rolling buffer consisting of the elements that arrived in the last $4b$ steps.
--
--   This feasibility fact says that the algorithm assembled from the local programs never selects an element before it arrives, as required of a clairvoyant trajectory.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/GlobalSchedule.lean#L63-L83 (`ConsistentSubmodular.ProtectedPrograms.arrived_bound`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_GlobalSchedule

open ConsistentSubmodular
open ConsistentSubmodular.ProtectedPrograms
variable {n b ell κ R B : ℕ} {f : Objective n} {β η : ℝ} {F : ℕ → ℝ}
variable {C : ProtectedClock F η b ell} (P : ProtectedPrograms f κ β C R B)

theorem ConsistentSubmodular.ProtectedPrograms.arrived_bound (t : ℕ) : P.selected t ⊆ arrivedPrefix n t := by sorry
