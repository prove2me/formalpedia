-- Prove2me | Theorems.Thm_ConsistentSubmodular_Objective_exists_forced_set
-- name    : ConsistentSubmodular.Objective.exists_forced_set
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:15.446824+00:00
-- url     : https://prove2.me/theorems/980daf76-95d9-485c-8c42-42c8325c74de
-- title:
--   Existence of a forced set with fewer than $H$ elements
-- statement:
--   Let $f$ be a nonnegative monotone submodular objective on $\{0,\dots,n-1\}$, let $U$ be a finite set and let $k,H$ be natural numbers with $0<H\le k$. Let $c,V\in\mathbb R$ satisfy
--
--   * $f(A)\le V$ for every $A\subseteq U$ with $|A|\le k$, and
--   * $V\le H\,c$.
--
--   Then there exists $D\subseteq U$ with $|D|<H$ such that every $e\in U\setminus D$ satisfies
--   $$f(D\cup\{e\})-f(D)\;\le\;c .$$
--
--   Every instance thus admits a forced set of fewer than $H$ elements, after which each remaining element has marginal at most $c$. This is the forced-set step of Appendix B.2.3.
--
--   **Formalization Note**: the scale bound $f(A)\le V$ is only assumed for sets of size at most $k$, and $H\le k$ guarantees that $D$ itself is such a set.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/ForcedSet.lean#L63-L85 (`ConsistentSubmodular.Objective.exists_forced_set`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem ConsistentSubmodular.Objective.exists_forced_set (U : Finset (Fin n)) (k H : ℕ) (hH : 0 < H) (hHk : H ≤ k)
    (c V : ℝ) (hscale : ∀ A ⊆ U, A.card ≤ k → f.value A ≤ V)
    (hpay : V ≤ (H : ℝ) * c) :
    ∃ D ⊆ U, D.card < H ∧
      ∀ e ∈ U, e ∉ D → f.value (insert e D) - f.value D ≤ c := by sorry
