-- Prove2me | Theorems.Thm_ConsistentSubmodular_HardInstance_value_le_before
-- name    : ConsistentSubmodular.HardInstance.value_le_before
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:49.656944+00:00
-- url     : https://prove2.me/theorems/459003e1-504d-49ee-aabf-821410790b63
-- title:
--   Value of a family of tiny sets before $U_0$ arrives
-- statement:
--   In the hard stream on $3k+2$ elements, let $u_0,u_1,u_2\ge0$ be the weights of the three groups of cells, and let $f_u(T)=\sum_g u_g\cdot\#\{\text{cells of group } g \text{ covered by } T\}$ be the weighted coverage. Let $S$ be a family all of whose elements have position less than $3k$, that is, a family of tiny sets only. Then
--   $$f_u(S)\le u_0\,c_0(S)+u_1\,c_1(S)+u_2\,c_2(S),$$
--   where $c_g(S)$ is the number of tiny sets of group $g$ in $S$.
--
--   Before $U_0$ arrives, a family of tiny sets covers at most one cell per set, which gives this bound. It is used for the value of an algorithm at time $3k$ in Appendix A.2.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Impossibility/HardStream.lean#L272-L296 (`ConsistentSubmodular.HardInstance.value_le_before`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Impossibility_HardStream

open scoped BigOperators
open Finset
open ConsistentSubmodular ConsistentSubmodular.HardInstance
variable {k : ℕ} {u : Fin 3 → ℝ}

theorem ConsistentSubmodular.HardInstance.value_le_before (hu : ∀ g, 0 ≤ u g) (S : Finset (Fin (3 * k + 2)))
    (hS : ∀ e ∈ S, e.val < 3 * k) :
    weightedValue k u S ≤
      u 0 * tinyCount k 0 S + u 1 * tinyCount k 1 S + u 2 * tinyCount k 2 S := by sorry
