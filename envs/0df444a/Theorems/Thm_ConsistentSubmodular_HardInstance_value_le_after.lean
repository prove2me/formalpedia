-- Prove2me | Theorems.Thm_ConsistentSubmodular_HardInstance_value_le_after
-- name    : ConsistentSubmodular.HardInstance.value_le_after
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:25:12.716947+00:00
-- url     : https://prove2.me/theorems/312bc2b2-23fb-4b50-8971-4787ad9c5402
-- title:
--   Value of a family at the end of the hard stream
-- statement:
--   In the hard stream on $3k+2$ elements, let $u_0,u_1,u_2\ge0$ be the weights of the three groups of cells and $f_u$ the weighted coverage. For every family $S$ of stream elements,
--   $$f_u(S)\le u_0\,k+u_1\,k+u_2\,c_2(S),$$
--   where $c_2(S)$ is the number of tiny sets of group $2$ in $S$.
--
--   At the end, groups $0$ and $1$ contribute at most their total weight $k u_0$ and $k u_1$, and group $2$ is covered only by its tiny sets. This is used for the value at time $3k+2$ in Appendix A.2.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Impossibility/HardStream.lean#L320-L336 (`ConsistentSubmodular.HardInstance.value_le_after`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Impossibility_HardStream

open scoped BigOperators
open Finset
open ConsistentSubmodular ConsistentSubmodular.HardInstance
variable {k : ℕ} {u : Fin 3 → ℝ}

theorem ConsistentSubmodular.HardInstance.value_le_after (hu : ∀ g, 0 ≤ u g) (S : Finset (Fin (3 * k + 2))) :
    weightedValue k u S ≤ u 0 * k + u 1 * k + u 2 * tinyCount k 2 S := by sorry
