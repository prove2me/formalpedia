-- Prove2me | Theorems.Thm_ConsistentSubmodular_type_expectation_le_independent_union
-- name    : ConsistentSubmodular.type_expectation_le_independent_union
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:32.77926+00:00
-- url     : https://prove2.me/theorems/bb20994b-73f3-43d3-b7e4-ebf0aff448e8
-- title:
--   Independent element coins dominate type coins in expected value
-- statement:
--   Let $f$ be a nonnegative monotone submodular objective on $[n]$, let $O_i\subseteq[n]$ ($i\in\iota$) be cores, possibly overlapping or repeated, let $U\subseteq\iota$ be finite, $p_i\in[0,1]$ for $i\in U$, and $B\subseteq[n]$. Let $I\subseteq U$ contain each $i$ independently with probability $p_i$, and let $S\subseteq[n]$ contain each element $e$ independently with probability
--   $$\pi_e=1-\prod_{i\in U,\ e\in O_i}(1-p_i).$$
--   Then
--
--   $$\mathbb{E}\Big[f\Big(B\cup\bigcup_{i\in I}O_i\Big)\Big]\;\le\;\mathbb{E}\big[f(B\cup S)\big].$$
--
--   Replacing every common core coin by independent element coins that have the same marginal inclusion probabilities can only increase the expected submodular value.
--
--   This is the central comparison between type mixtures and physical (element-level) sampling, and it underlies the rounding of fractional windows.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Basic/PhysicalSampling.lean#L162-L209 (`ConsistentSubmodular.type_expectation_le_independent_union`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_PhysicalSampling

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]
variable {n : ℕ}

theorem ConsistentSubmodular.type_expectation_le_independent_union (f : Objective n)
    (cores : ι → Finset (Fin n)) (U : Finset ι) (p : ι → ℝ)
    (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) (B : Finset (Fin n)) :
    sampleExpectation U p (fun I => f.value (B ∪ I.biUnion cores)) ≤
      sampleAdd Finset.univ (unionProbability cores U p) f.value B := by sorry
