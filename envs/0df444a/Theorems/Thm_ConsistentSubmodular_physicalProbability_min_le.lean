-- Prove2me | Theorems.Thm_ConsistentSubmodular_physicalProbability_min_le
-- name    : ConsistentSubmodular.physicalProbability_min_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:21.493079+00:00
-- url     : https://prove2.me/theorems/50898a17-440c-4eef-81de-559510fd6e25
-- title:
--   Physical inclusion probability of a coordinatewise minimum is dominated by both minima
-- statement:
--   Let $O_0,\dots,O_m\subseteq[n]$ be cores (overlaps and repetitions allowed), let $p,q\in\mathbb{R}^{m+1}$ be type vectors and $e\in[n]$. The physical inclusion probability of element $e$ under a type vector $p$ is $z_e(p)=\sum_{i:\,e\in O_i}p_i$. Then
--
--   $$z_e\big(\min(p,q)\big)\;\le\;\min\big(z_e(p),\,z_e(q)\big),$$
--
--   where $\min(p,q)$ is the coordinatewise minimum, $(\min(p,q))_i=\min(p_i,q_i)$. No sign or normalization condition on $p,q$ is needed.
--
--   The statement says that passing to the coordinatewise minimum of two type vectors can only decrease every physical inclusion probability, even when cores overlap. It is used when comparing safe paths through shared thresholds.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Basic/PhysicalMap.lean#L77-L93 (`ConsistentSubmodular.physicalProbability_min_le`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Basic_PhysicalMap

open scoped BigOperators
open ConsistentSubmodular
variable {n m : ℕ}

theorem ConsistentSubmodular.physicalProbability_min_le
    (cores : Fin (m + 1) → Finset (Fin n)) (p q : Point m) (e : Fin n) :
    physicalProbability cores (fun i => min (p i) (q i)) e ≤
      min (physicalProbability cores p e) (physicalProbability cores q e) := by sorry
