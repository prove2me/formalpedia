-- Prove2me | Theorems.Thm_ConsistentSubmodular_IntervalSelection_benchmark_le_of_zero
-- name    : ConsistentSubmodular.IntervalSelection.benchmark_le_of_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:44.755263+00:00
-- url     : https://prove2.me/theorems/16b1a728-475b-482e-a810-369f7a32255f
-- title:
--   Degenerate case $f(O_0)=0$: no candidate adds value
-- statement:
--   Let $W$ be a window instance with stages $0,\dots,m$, candidates $O_j$, arrival prefixes $R_j$ and benchmarks $P_j=f(O_j\cup R_j)$. If $P_0=f(O_0)\le 0$, then for every stage $j$
--   $$f(O_j\cup R_j)\;\le\; f(R_j).$$
--
--   If $f(O_0)=0$, the singletons of every candidate are worth no more than $\emptyset$, so no candidate adds value to the arrivals. This is the degenerate case that precedes the normalized form of the linear program (1) in the proof of Lemma 2.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/IntervalSelection.lean#L122-L139 (`ConsistentSubmodular.IntervalSelection.benchmark_le_of_zero`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open ConsistentSubmodular
variable {n : ℕ} (W : WindowInstance n)

theorem ConsistentSubmodular.IntervalSelection.benchmark_le_of_zero (h0 : W.benchmark 0 ≤ 0) (j : Fin (W.lastStage + 1)) :
    W.benchmark j ≤ W.objective.value (W.arrivals j) := by sorry
