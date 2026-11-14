-- Prove2me | Theorems.Thm_ConsistentSubmodular_IntervalSelection_isAdditionRobust_of_candidates
-- name    : ConsistentSubmodular.IntervalSelection.isAdditionRobust_of_candidates
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:25:08.146004+00:00
-- url     : https://prove2.me/theorems/832313ce-a57e-4d79-a309-5463e733d397
-- title:
--   From a distribution over candidates to addition robustness
-- statement:
--   Let $W$ be a window instance with stages $0,\dots,m$, candidates $O_i$ (sets of at most $\kappa$ present elements), arrival prefixes $R_j$ and benchmarks $P_j=f(O_j\cup R_j)$. Let $\alpha\in\mathbb R$ and let $p$ be a probability vector on $\{0,\dots,m\}$ such that for every stage $j$
--   $$\alpha\,P_j\;\le\;\sum_i p_i\,f(O_i\cup R_j).$$
--   Then there are weights $w$ on subsets of the arrived elements which form an $\alpha$-addition-robust distribution for $W$ (Definition 2.1): nonnegative, summing to $1$, supported on sets $S\subseteq V_{\mathrm{now}}$ with $|S|\le\kappa$, and satisfying $\alpha P_j\le\sum_S w(S)\,f(S\cup R_j)$ for all $j$.
--
--   The distribution is obtained by pushing $p$ forward along $i\mapsto O_i$. This closes the proof of Lemma 2.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/IntervalSelection.lean#L291-L316 (`ConsistentSubmodular.IntervalSelection.isAdditionRobust_of_candidates`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open ConsistentSubmodular

theorem ConsistentSubmodular.IntervalSelection.isAdditionRobust_of_candidates {α : ℝ} {n : ℕ} {W : WindowInstance n}
    {p : Point W.lastStage} (hp : IsSimplex p)
    (h : ∀ j, α * W.benchmark j ≤
      ∑ i, p i * W.objective.value (W.candidate i ∪ W.arrivals j)) :
    ∃ w, W.IsAdditionRobust α w := by sorry
