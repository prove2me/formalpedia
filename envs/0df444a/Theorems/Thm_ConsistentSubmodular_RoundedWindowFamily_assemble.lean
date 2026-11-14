-- Prove2me | Theorems.Thm_ConsistentSubmodular_RoundedWindowFamily_assemble
-- name    : ConsistentSubmodular.RoundedWindowFamily.assemble
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:35.037203+00:00
-- url     : https://prove2.me/theorems/07764dd7-82bc-4fb0-9383-d9430674f6a7
-- title:
--   Assembling rounded windows and bridges into protected programs
-- statement:
--   Let $f$ be an objective on $[n]$, $C$ a protected clock with parameters $(F,\eta,b,\ell)$, and $\kappa,B,L,R\in\mathbb N$, $\beta\in\mathbb R$. Let $W$ be a rounded window family for $(f,\kappa,\beta,C,B,L)$ (entry and exit operation paths for each window, with cardinality at most $B$, arrived elements only, total length at most $L\kappa$, and the stated value guarantees at the window ends and at checkpoints), and let $T$ be a rounded bridge family for $W$ (paths from the end of the exit path of window $i$ to the start of the entry path of window $i+1$, of length at most $L\kappa$). If
--   $$\kappa\le B\qquad\text{and}\qquad (3L+1)\,\kappa\le R\,\ell,$$
--   then there exists a family of protected programs, i.e. the type `ProtectedPrograms f κ β C R B` is nonempty.
--
--   The concatenation of entry, exit and bridge paths yields one path per clock interval of length at most $(3L+1)\kappa\le R\ell$, so that all steps can be scheduled with a uniform per-update rate $R$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/ProgramAssembly.lean#L49-L134 (`ConsistentSubmodular.RoundedWindowFamily.assemble`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_ProgramAssembly

open ConsistentSubmodular
open ConsistentSubmodular.RoundedWindowFamily
variable {n b ell κ B L R : ℕ} {f : Objective n} {β η : ℝ}
variable {F : ℕ → ℝ} {C : ProtectedClock F η b ell}
variable (W : RoundedWindowFamily f κ β C B L) (T : RoundedBridgeFamily W)
include W T

theorem ConsistentSubmodular.RoundedWindowFamily.assemble (hκB : κ ≤ B) (hrate : (3 * L + 1) * κ ≤ R * ell) :
    Nonempty (ProtectedPrograms f κ β C R B) := by sorry
