-- Prove2me | Theorems.Thm_ConsistentSubmodular_IntervalSelection_value_le_objective
-- name    : ConsistentSubmodular.IntervalSelection.value_le_objective
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:08.120636+00:00
-- url     : https://prove2.me/theorems/c70b61b8-be04-4526-9bc5-e60dd4283bf6
-- title:
--   Claim (4) — the interval value is a lower bound on $f(O_i\cup R_j)$
-- statement:
--   Let $W$ be a window instance with stages $0,\dots,m$, candidates $O_i$, arrivals $R_j$ and benchmarks $P_i=f(O_i\cup R_i)$. Let $p$ be a probability vector on the stages, and let $I$ be the interval instance with intervals $[\ell_i,r_i]=[f(R_i),\,f(O_i\cup R_i)]$ and distribution $p$, with values $v(i,j)=\ell_j+\max\bigl(0,\,r_i-\max(\ell_i,\ell_j)\bigr)$. Then for all stages $i,j\in\{0,\dots,m\}$
--   $$v(i,j)\;\le\; f(O_i\cup R_j).$$
--
--   This is claim (4) in the proof of Lemma 2: for $j\le i$ it follows from diminishing returns, and for $j\ge i$ from monotonicity. It lets the interval-selection instance serve as a lower bound for the addition-robust objective.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/IntervalSelection.lean#L94-L120 (`ConsistentSubmodular.IntervalSelection.value_le_objective`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_AdaptivityGap_IntervalSelection

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.IntervalSelection
variable {n : ℕ} (W : WindowInstance n)

theorem ConsistentSubmodular.IntervalSelection.value_le_objective (p : Point W.lastStage) (hp : IsSimplex p)
    (i j : Fin (W.lastStage + 1)) :
    (windowIntervals W p hp).value i j ≤ W.objective.value (W.candidate i ∪ W.arrivals j) := by sorry
