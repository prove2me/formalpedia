-- Prove2me | Theorems.Thm_ConsistentSubmodular_WindowSamples_toRounded
-- name    : ConsistentSubmodular.WindowSamples.toRounded
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:53.636491+00:00
-- url     : https://prove2.me/theorems/b73f4b22-e52e-4a8a-add6-73b9c542a9e5
-- title:
--   From window samples to a rounded window
-- statement:
--   Let $W$ be a fractional window with parameters $(f,\mathrm{old},Q,\kappa,N,T,\mathrm{initial},\mathrm{terminal},\alpha,S)$, and let $\mathrm{Smp}$ be window samples for $W$ with forced-element reserve $H$: a forced set of fewer than $H$ elements together with sampled entry and exit pieces with the cardinality, cost, intersection and checkpoint guarantees. If $H\le\kappa$, then there exists a rounded window for $W$ with reserve $H$ and length coefficient $100S+10$ (`windowLengthBound S`), i.e. `Nonempty (RoundedWindow W H (windowLengthBound S))`.
--
--   The sampled pieces are converted into physical operation paths; the cost bound $8S\kappa$ on the recourse between consecutive pieces is what yields the length bound $(100S+10)\kappa$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/WindowOperationAssembly.lean#L93-L196 (`ConsistentSubmodular.WindowSamples.toRounded`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_RoundedWindow
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_WindowSamples

open scoped BigOperators
open ConsistentSubmodular
open ConsistentSubmodular.WindowSamples
variable {n κ N T S H : ℕ} {α : ℝ} {f : Objective n} {old initial terminal : Finset (Fin n)}
  {Q : ℕ → Finset (Fin n)} {hQ : Monotone Q}
  {W : FractionalWindow f old Q hQ κ N T initial terminal α S}
  (Smp : WindowSamples W H)
include Smp

theorem ConsistentSubmodular.WindowSamples.toRounded (hκ : H ≤ κ) : Nonempty (RoundedWindow W H (windowLengthBound S)) := by sorry
