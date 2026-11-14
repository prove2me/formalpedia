-- Prove2me | Theorems.Thm_ConsistentSubmodular_HardInstance_value_le_middle
-- name    : ConsistentSubmodular.HardInstance.value_le_middle
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:37.262916+00:00
-- url     : https://prove2.me/theorems/ebc64eb8-2415-48b1-bf3b-6fe1e9b2eb33
-- title:
--   Value of a family before $U_1$ arrives
-- statement:
--   In the hard stream on $3k+2$ elements, let $u_0,u_1,u_2\ge0$ be the weights of the three groups of cells and $f_u$ the weighted coverage. Let $S$ be a family all of whose elements have position less than $3k+1$ (tiny sets and possibly $U_0$, but not $U_1$). Then
--   $$f_u(S)\le u_0\,k+u_1\,c_1(S)+u_2\,c_2(S),$$
--   where $c_g(S)$ is the number of tiny sets of group $g$ in $S$.
--
--   Before $U_1$ arrives, group $0$ contributes at most its total weight $k u_0$, and groups $1$ and $2$ are covered only by their own tiny sets. This is used for the value at time $3k+1$ in Appendix A.2.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Impossibility/HardStream.lean#L298-L318 (`ConsistentSubmodular.HardInstance.value_le_middle`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Impossibility_HardStream

open scoped BigOperators
open Finset
open ConsistentSubmodular ConsistentSubmodular.HardInstance
variable {k : ℕ} {u : Fin 3 → ℝ}

theorem ConsistentSubmodular.HardInstance.value_le_middle (hu : ∀ g, 0 ≤ u g) (S : Finset (Fin (3 * k + 2)))
    (hS : ∀ e ∈ S, e.val < 3 * k + 1) :
    weightedValue k u S ≤ u 0 * k + u 1 * tinyCount k 1 S + u 2 * tinyCount k 2 S := by sorry
