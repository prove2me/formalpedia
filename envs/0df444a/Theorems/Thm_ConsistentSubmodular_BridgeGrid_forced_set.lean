-- Prove2me | Theorems.Thm_ConsistentSubmodular_BridgeGrid_forced_set
-- name    : ConsistentSubmodular.BridgeGrid.forced_set
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:11.062371+00:00
-- url     : https://prove2.me/theorems/748f97a1-1dd9-4126-b515-cb33b6b7202f
-- title:
--   Forced set from a global union-value bound
-- statement:
--   Let $f$ be a nonnegative monotone submodular objective on $\{0,\dots,n-1\}$, let $U$ be a finite set, let $H\ge 1$ and let $V>0$ with $f(U)\le 2V$. Then there is $D\subseteq U$ with $|D|\le H$ such that every $e\in U\setminus D$ satisfies
--   $$f(D\cup\{e\})-f(D)\;\le\;\frac{2V}{H}.$$
--
--   A global bound on the value of the union suffices for a bounded forced set; no cardinality optimum is needed in the two-core bridge.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/BridgeGrid.lean#L65-L83 (`ConsistentSubmodular.BridgeGrid.forced_set`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_MainStatements

open scoped BigOperators
open ConsistentSubmodular
variable {n : ℕ}

theorem ConsistentSubmodular.BridgeGrid.forced_set (f : Objective n) (U : Finset (Fin n)) (H : ℕ) (hH : 0 < H)
    (V : ℝ) (hV : 0 < V) (hU : f.value U ≤ 2 * V) :
    ∃ D ⊆ U, D.card ≤ H ∧ ∀ e ∈ U, e ∉ D →
      f.value (insert e D) - f.value D ≤ 2 * V / H := by sorry
