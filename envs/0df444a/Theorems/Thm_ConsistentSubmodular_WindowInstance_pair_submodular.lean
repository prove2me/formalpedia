-- Prove2me | Theorems.Thm_ConsistentSubmodular_WindowInstance_pair_submodular
-- name    : ConsistentSubmodular.WindowInstance.pair_submodular
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:16.042202+00:00
-- url     : https://prove2.me/theorems/b33ae640-a39e-4d94-9cd4-60658ec0055f
-- title:
--   Residual overlap of two candidates at a stage is nonnegative
-- statement:
--   Let $W$ be a window instance with objective $f$, arrivals $R_0\subseteq\dots\subseteq R_m$ and candidates $O_0,\dots,O_m$. For all stages $j,a,b\in\{0,\dots,m\}$ (not necessarily distinct),
--
--   $$f\big(R_j\cup(O_a\cup O_b)\big)+f(R_j)\;\le\;f(R_j\cup O_a)+f(R_j\cup O_b).$$
--
--   Equivalently, the residual overlap $o=f(R_j\cup O_a)+f(R_j\cup O_b)-f(R_j\cup O_a\cup O_b)-f(R_j)$ is nonnegative.
--
--   This follows from submodularity of $f$, and is the sign condition used in the two-type interpolation formula (23).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Basic/WindowBounds.lean#L217-L233 (`ConsistentSubmodular.WindowInstance.pair_submodular`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]
open ConsistentSubmodular.WindowInstance
variable {n : ℕ} (W : WindowInstance n)

theorem ConsistentSubmodular.WindowInstance.pair_submodular (j a b : Fin (W.lastStage + 1)) :
    W.objective.value (W.arrivals j ∪ (W.candidate a ∪ W.candidate b)) +
        W.objective.value (W.arrivals j) ≤
      W.objective.value (W.arrivals j ∪ W.candidate a) +
        W.objective.value (W.arrivals j ∪ W.candidate b) := by sorry
