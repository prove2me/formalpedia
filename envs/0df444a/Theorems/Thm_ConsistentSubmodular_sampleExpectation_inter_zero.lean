-- Prove2me | Theorems.Thm_ConsistentSubmodular_sampleExpectation_inter_zero
-- name    : ConsistentSubmodular.sampleExpectation_inter_zero
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:31.50888+00:00
-- url     : https://prove2.me/theorems/8f157405-f3ea-4d04-bdf9-a15a3f5e625c
-- title:
--   Sampling coins with zero probability outside $U$ may be discarded
-- statement:
--   Let $U,V$ be finite sets, $p:\iota\to\mathbb{R}$ with $p_i=0$ for every $i\notin U$, and $v:2^\iota\to\mathbb{R}$. Writing $\mathbb{E}_V^p[v]=\sum_{S\subseteq V}\big(\prod_{i\in S}p_i\prod_{i\in V\setminus S}(1-p_i)\big)v(S)$ for the expectation over the random subset of $V$ with independent inclusion probabilities $p_i$, we have
--
--   $$\mathbb{E}_V^p[v]\;=\;\mathbb{E}_{V\cap U}^p[v].$$
--
--   Elements with probability zero never enter the sample and contribute a factor $1$, so the sampling universe can be restricted to the support. This is a bookkeeping reduction in the sampling-operator calculus.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Basic/PhysicalSampling.lean#L34-L50 (`ConsistentSubmodular.sampleExpectation_inter_zero`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_SamplingOperators

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]

theorem ConsistentSubmodular.sampleExpectation_inter_zero (U V : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∉ U, p i = 0) (v : Finset ι → ℝ) :
    sampleExpectation V p v = sampleExpectation (V ∩ U) p v := by sorry
