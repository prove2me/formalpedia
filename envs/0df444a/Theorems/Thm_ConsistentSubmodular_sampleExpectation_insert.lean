-- Prove2me | Theorems.Thm_ConsistentSubmodular_sampleExpectation_insert
-- name    : ConsistentSubmodular.sampleExpectation_insert
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:27.98541+00:00
-- url     : https://prove2.me/theorems/aa06ab49-c54b-4174-811b-b98eefcd1e8d
-- title:
--   Recursion for the finite sample expectation when adding one coin
-- statement:
--   Let $U$ be a finite set, $e\notin U$, $p:\iota\to\mathbb{R}$ and $v:2^{\iota}\to\mathbb{R}$. For a finite set $U$ write
--   $$\mathbb{E}_U^p[v]=\sum_{S\subseteq U}\Big(\prod_{i\in S}p_i\prod_{i\in U\setminus S}(1-p_i)\Big)v(S),$$
--   the expectation of $v$ over the random subset of $U$ containing each $i$ independently with probability $p_i$. Then
--
--   $$\mathbb{E}_{U\cup\{e\}}^p[v]\;=\;(1-p_e)\,\mathbb{E}_U^p[v]\;+\;p_e\,\mathbb{E}_U^p\big[S\mapsto v(S\cup\{e\})\big].$$
--
--   No range condition on $p$ is assumed.
--
--   This is the one-coin conditioning identity (condition on whether $e$ is sampled) that drives induction on the size of the sampling universe in the sampling-operator calculus.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Basic/SamplingOperators.lean#L56-L89 (`ConsistentSubmodular.sampleExpectation_insert`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_SamplingOperators

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]

theorem ConsistentSubmodular.sampleExpectation_insert (U : Finset ι) {e : ι} (he : e ∉ U)
    (p : ι → ℝ) (v : Finset ι → ℝ) :
    sampleExpectation (insert e U) p v =
      (1 - p e) * sampleExpectation U p v + p e * sampleExpectation U p (fun S => v (insert e S)) := by sorry
