-- Prove2me | Theorems.Thm_ConsistentSubmodular_Objective_exists_penalized_core
-- name    : ConsistentSubmodular.Objective.exists_penalized_core
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:08.346203+00:00
-- url     : https://prove2.me/theorems/92e564d4-b479-45b6-8ada-62723f77dc6c
-- title:
--   Existence of a penalized core with marginal thresholds at level $c$
-- statement:
--   Let $f$ be a nonnegative monotone submodular objective on $\{0,\dots,n-1\}$, let $U$ be a finite set and let $c\in\mathbb R$. Then there is a set $D\subseteq U$ such that
--
--   1. every $e\in U\setminus D$ has insertion marginal at most the penalty: $f(D\cup\{e\})-f(D)\le c$, and
--   2. every $e\in D$ has removal marginal strictly above the penalty: $c<f(D)-f(D\setminus\{e\})$.
--
--   Such a $D$ is obtained as a smallest maximizer of the penalized objective $A\mapsto f(A)-c|A|$ over subsets of $U$. This replaces the greedy construction of the forced set $D$ in Appendix B.2.3: elements of $D$ are forced because each contributes more than $c$, and no element outside it contributes more than $c$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/ForcedSet.lean#L16-L61 (`ConsistentSubmodular.Objective.exists_penalized_core`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem ConsistentSubmodular.Objective.exists_penalized_core (U : Finset (Fin n)) (c : ℝ) :
    ∃ D ⊆ U,
      (∀ e ∈ U, e ∉ D → f.value (insert e D) - f.value D ≤ c) ∧
      (∀ e ∈ D, c < f.value D - f.value (D.erase e)) := by sorry
