-- Prove2me | Theorems.Thm_ConsistentSubmodular_sum_weight_disjoint
-- name    : ConsistentSubmodular.sum_weight_disjoint
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:19.019676+00:00
-- url     : https://prove2.me/theorems/25acad39-5369-4764-9e08-777f7a9544be
-- title:
--   Total Bernoulli weight of subsets avoiding $L$ equals $\prod_{i\in L}(1-p_i)$
-- statement:
--   Let $\iota$ be a finite type, $p:\iota\to\mathbb{R}$ any real weights and $L\subseteq\iota$ a finite set. Write $w_p(S)=\prod_{i\in S}p_i\prod_{i\notin S}(1-p_i)$ for the Bernoulli weight of $S\subseteq\iota$. Then
--
--   $$\sum_{S\subseteq\iota,\ S\cap L=\emptyset} w_p(S)\;=\;\prod_{i\in L}(1-p_i).$$
--
--   No range restriction on $p$ is assumed. In probabilistic terms, when $p_i\in[0,1]$ the left side is the probability that an independent random set $I(p)$ misses every element of $L$.
--
--   This identity is the basic marginalization step for the finite expectation $\mathbb{E}[g(I(p))]$ used throughout the mixture and physical-sampling arguments.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Basic/FiniteExpectation.lean#L60-L84 (`ConsistentSubmodular.sum_weight_disjoint`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_FiniteExpectation

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem ConsistentSubmodular.sum_weight_disjoint (p : ι → ℝ) (L : Finset ι) :
    (∑ S : Finset ι, if Disjoint S L then bernoulliWeight p S else 0) =
      ∏ i ∈ L, (1 - p i) := by sorry
