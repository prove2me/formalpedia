-- Prove2me | Theorems.Thm_ConsistentSubmodular_IntervalSelection_candidates_of_gap_pos
-- name    : ConsistentSubmodular.IntervalSelection.candidates_of_gap_pos
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:32.485294+00:00
-- url     : https://prove2.me/theorems/25fd55b9-e8bd-4cbc-8eef-9cf035068643
-- title:
--   Main case of Lemma 2 ($\kappa\ge1$, $f(O_0)>0$)
-- statement:
--   Let $W$ be a window instance with stages $0,\dots,m$, candidates $O_i$, arrival prefixes $R_j$ and benchmarks $P_j=f(O_j\cup R_j)$. Let $\alpha\ge0$ be such that every interval-selection instance has adaptivity gap at least $\alpha$. Assume the core budget satisfies $\kappa\ge1$ and $f(O_0)>0$. Then there is a probability vector $p$ on $\{0,\dots,m\}$ such that for every stage $j$
--   $$\alpha\,P_j\;\le\;\sum_i p_i\,f(O_i\cup R_j).$$
--
--   In the proof of Lemma 2, every distribution $\beta$ of the adversary meets a row worth at least $\alpha$, so Lemma 5 gives $\rho^\star\ge\alpha$, and the distribution of Lemma 5 attaining $\rho^\star$ is the required $p$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/AdaptivityGap/IntervalSelection.lean#L252-L274 (`ConsistentSubmodular.IntervalSelection.candidates_of_gap_pos`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open ConsistentSubmodular
variable {n : ℕ} (W : WindowInstance n)

theorem ConsistentSubmodular.IntervalSelection.candidates_of_gap_pos {α : ℝ} (hα0 : 0 ≤ α)
    (hgap : ∀ (N : ℕ) (I : IntervalInstance N), α ≤ I.adaptivityGap)
    (hκ : 1 ≤ W.coreBudget) (h0 : 0 < W.objective.value (W.candidate 0)) :
    ∃ p : Point W.lastStage, IsSimplex p ∧
      ∀ j, α * W.benchmark j ≤ ∑ i, p i * W.objective.value (W.candidate i ∪ W.arrivals j) := by sorry
