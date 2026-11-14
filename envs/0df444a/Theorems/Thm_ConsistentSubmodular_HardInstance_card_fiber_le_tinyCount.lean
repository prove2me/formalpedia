-- Prove2me | Theorems.Thm_ConsistentSubmodular_HardInstance_card_fiber_le_tinyCount
-- name    : ConsistentSubmodular.HardInstance.card_fiber_le_tinyCount
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:24:38.749475+00:00
-- url     : https://prove2.me/theorems/7e1e4792-ccbe-43aa-9e04-18581fd4aab6
-- title:
--   Cells of a group not covered by its large set are covered by tiny sets
-- statement:
--   Consider the hard stream of $3k+2$ elements: the tiny sets at positions $gk+b<3k$ (for $g\in\{0,1,2\}$ and $b\in\{0,\dots,k-1\}$), each covering the single cell $(g,b)$; the large set $U_0$ at position $3k$, covering all cells of group $0$; and the large set $U_1$ at position $3k+1$, covering all cells of group $1$. Let $S$ be a family of stream elements and $g\in\{0,1,2\}$, and assume that the large set of group $g$ is not in $S$, that is, no element of $S$ has position $3k+g$. Then the number of cells of group $g$ covered by $S$ is at most the number $c_g(S)$ of tiny sets of group $g$ in $S$:
--   $$\bigl|\{\text{cells of group } g \text{ covered by } S\}\bigr|\le c_g(S).$$
--
--   Without the large set of group $g$, each cell of that group is covered only by its own tiny set, one cell per set. This is a basic counting step in the bounds on the value of a family in the hard instance of Appendix A.2.
--
--   **Formalization Note** For $g=2$ there is no large set (position $3k+2$ does not exist), so the hypothesis is vacuous.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Randomized/Impossibility/HardStream.lean#L119-L155 (`ConsistentSubmodular.HardInstance.card_fiber_le_tinyCount`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Randomized_Impossibility_HardStream

open scoped BigOperators
open Finset
open ConsistentSubmodular ConsistentSubmodular.HardInstance

theorem ConsistentSubmodular.HardInstance.card_fiber_le_tinyCount {k : ℕ} (S : Finset (Fin (3 * k + 2))) (g : Fin 3)
    (hfull : ∀ e ∈ S, e.val ≠ 3 * k + g.val) :
    (fiber (S.biUnion (elementCells k)) g).card ≤ tinyCount k g S := by sorry
