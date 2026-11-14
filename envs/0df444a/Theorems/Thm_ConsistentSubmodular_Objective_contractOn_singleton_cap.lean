-- Prove2me | Theorems.Thm_ConsistentSubmodular_Objective_contractOn_singleton_cap
-- name    : ConsistentSubmodular.Objective.contractOn_singleton_cap
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:22:44.830726+00:00
-- url     : https://prove2.me/theorems/9e86c172-6c00-4d43-873b-c04ed2e1b219
-- title:
--   Singleton marginals of a contracted objective stay below the cap
-- statement:
--   Let $f$ be a nonnegative monotone submodular function on subsets of $[n]$, let $U,D,Q\subseteq[n]$ and $c\ge0$, and write $f_{U,B}(S)=f\big(B\cup(S\cap U)\big)-f(B)$ for the contraction of the buffer $B$ on the ground set $U$. Assume that
--
--   $$f(D\cup\{e\})-f(D)\le c\qquad\text{for all } e\in U\setminus D .$$
--
--   Then for every $e\in[n]$,
--
--   $$f_{U,\,D\cup Q}(\{e\})-f_{U,\,D\cup Q}(\emptyset)\;\le\;c .$$
--
--   Contracting a larger buffer $D\cup Q$ therefore keeps the marginal cap $c$ valid. The cap is the parameter $L$ in the lower-tail concentration bound used for rounding.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Reduction/SamplingScale.lean#L65-L78 (`ConsistentSubmodular.Objective.contractOn_singleton_cap`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Reduction_SamplingScale

open scoped BigOperators
open ConsistentSubmodular ConsistentSubmodular.Objective
variable {n : ℕ} (f : Objective n)

theorem ConsistentSubmodular.Objective.contractOn_singleton_cap (U D Q : Finset (Fin n)) {c : ℝ} (hc : 0 ≤ c)
    (hcap : ∀ e ∈ U, e ∉ D → f.value (insert e D) - f.value D ≤ c) :
    ∀ e, (f.contractOn U (D ∪ Q)).value {e} - (f.contractOn U (D ∪ Q)).value ∅ ≤ c := by sorry
