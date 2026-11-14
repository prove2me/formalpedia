-- Prove2me | Theorems.Thm_ConsistentSubmodular_finiteExpectation_mem
-- name    : ConsistentSubmodular.finiteExpectation_mem
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:22.091502+00:00
-- url     : https://prove2.me/theorems/2b2dc721-7366-42aa-8a61-cb8a1da70fcd
-- title:
--   A Bernoulli random set contains $i$ with probability $p_i$
-- statement:
--   Let $\iota$ be a finite type, $p:\iota\to\mathbb{R}$ and $i\in\iota$. For the finite expectation
--   $$\mathbb{E}_p[g]=\sum_{I\subseteq\iota}\Big(\prod_{j\in I}p_j\prod_{j\notin I}(1-p_j)\Big)g(I),$$
--   we have, for the indicator $g(I)=\mathbf 1[i\in I]$,
--
--   $$\mathbb{E}_p\big[\mathbf 1[i\in I]\big]\;=\;p_i.$$
--
--   No range condition on $p$ is assumed. This records that the random set $I(p)$, containing each index independently with probability $p_i$, contains $i$ with probability exactly $p_i$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Basic/WindowBounds.lean#L55-L71 (`ConsistentSubmodular.finiteExpectation_mem`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_FiniteExpectation

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]

theorem ConsistentSubmodular.finiteExpectation_mem [Fintype ι] (p : ι → ℝ) (i : ι) :
    finiteExpectation p (fun I => if i ∈ I then 1 else 0) = p i := by sorry
