-- Prove2me | Theorems.Thm_ConsistentSubmodular_unionProbability_mem_unitInterval
-- name    : ConsistentSubmodular.unionProbability_mem_unitInterval
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:32.535765+00:00
-- url     : https://prove2.me/theorems/cf123e9c-c87b-4108-a0d7-2324742a7793
-- title:
--   Union inclusion probabilities lie in $[0,1]$
-- statement:
--   Let $O_i\subseteq[n]$ ($i\in\iota$) be cores, $U\subseteq\iota$ finite, $p:\iota\to\mathbb{R}$ with $0\le p_i\le1$ for all $i\in U$, and $e\in[n]$. Define the union probability
--   $$\pi_e\;=\;1-\prod_{i\in U,\ e\in O_i}(1-p_i).$$
--   Then $0\le\pi_e\le1$.
--
--   Here $\pi_e$ is the probability that $e$ belongs to $\bigcup_{i\in I}O_i$ when each $i\in U$ is selected independently with probability $p_i$; the statement shows that these numbers are legitimate inclusion probabilities.
--
--   It is a well-definedness fact used before the independent-union comparison with element coins.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Basic/PhysicalSampling.lean#L122-L143 (`ConsistentSubmodular.unionProbability_mem_unitInterval`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_PhysicalSampling

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]
variable {n : ℕ}
omit [DecidableEq ι]

theorem ConsistentSubmodular.unionProbability_mem_unitInterval (cores : ι → Finset (Fin n)) (U : Finset ι)
    (p : ι → ℝ) (hp : ∀ i ∈ U, 0 ≤ p i ∧ p i ≤ 1) (e : Fin n) :
    0 ≤ unionProbability cores U p e ∧ unionProbability cores U p e ≤ 1 := by sorry
