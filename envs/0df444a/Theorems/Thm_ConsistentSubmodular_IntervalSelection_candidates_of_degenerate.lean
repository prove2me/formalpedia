-- Prove2me | Theorems.Thm_ConsistentSubmodular_IntervalSelection_candidates_of_degenerate
-- name    : ConsistentSubmodular.IntervalSelection.candidates_of_degenerate
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:23:46.287062+00:00
-- url     : https://prove2.me/theorems/2065992a-9f51-46e5-82ff-cb37497a0049
-- title:
--   Degenerate case $f(O_0)=0$ of Lemma 2
-- statement:
--   Let $W$ be a window instance with stages $0,\dots,m$, candidates $O_i$, arrival prefixes $R_j$ and benchmarks $P_j=f(O_j\cup R_j)$. Let $\alpha\le 1$ and suppose $P_0=f(O_0)\le 0$. Then there is a probability vector $p$ on $\{0,\dots,m\}$ such that for every stage $j$
--   $$\alpha\,P_j\;\le\;\sum_i p_i\, f(O_i\cup R_j).$$
--
--   This is the degenerate case $\kappa\ge1$, $f(O_0)=0$ of Lemma 2: every distribution over the candidates works, for example the vertex $\delta_0$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/IntervalSelection.lean#L147-L162 (`ConsistentSubmodular.IntervalSelection.candidates_of_degenerate`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open ConsistentSubmodular
variable {n : ℕ} (W : WindowInstance n)

theorem ConsistentSubmodular.IntervalSelection.candidates_of_degenerate {α : ℝ} (hα1 : α ≤ 1) (h0 : W.benchmark 0 ≤ 0) :
    ∃ p : Point W.lastStage, IsSimplex p ∧
      ∀ j, α * W.benchmark j ≤ ∑ i, p i * W.objective.value (W.candidate i ∪ W.arrivals j) := by sorry
