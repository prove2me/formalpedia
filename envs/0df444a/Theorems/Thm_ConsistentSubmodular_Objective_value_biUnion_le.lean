-- Prove2me | Theorems.Thm_ConsistentSubmodular_Objective_value_biUnion_le
-- name    : ConsistentSubmodular.Objective.value_biUnion_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:19:19.74119+00:00
-- url     : https://prove2.me/theorems/0ec5b2a5-6d74-4312-a291-10781640b1ed
-- title:
--   Subadditivity of marginals after contracting a buffer
-- statement:
--   Let $f$ be a nonnegative monotone submodular objective on $[n]$, $Q\subseteq[n]$ a buffer, $O_0,\dots,O_{d-1}\subseteq[n]$ cores and $I\subseteq\{0,\dots,d-1\}$. Then
--
--   $$f\Big(Q\cup\bigcup_{i\in I}O_i\Big)\;\le\;f(Q)+\sum_{i\in I}\big(f(Q\cup O_i)-f(Q)\big).$$
--
--   Equivalently, $f(Q\cup\bigcup_{i\in I}O_i)-f(Q)\le\sum_{i\in I}\big(f(Q\cup O_i)-f(Q)\big)$: the marginal of a union of cores over $Q$ is at most the sum of the individual marginals.
--
--   This subadditivity after contracting $Q$ is the first ingredient of the mixture upper bound (22).
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Basic/WindowBounds.lean#L77-L93 (`ConsistentSubmodular.Objective.value_biUnion_le`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open ConsistentSubmodular
variable {ι : Type*} [DecidableEq ι]
open ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem ConsistentSubmodular.Objective.value_biUnion_le (Q : Finset (Fin n)) {d : ℕ} (cores : Fin d → Finset (Fin n))
    (I : Finset (Fin d)) :
    f.value (Q ∪ I.biUnion cores) ≤ f.value Q + ∑ i ∈ I, (f.value (Q ∪ cores i) - f.value Q) := by sorry
