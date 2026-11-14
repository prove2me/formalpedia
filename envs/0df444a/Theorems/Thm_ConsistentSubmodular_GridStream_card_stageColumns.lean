-- Prove2me | Theorems.Thm_ConsistentSubmodular_GridStream_card_stageColumns
-- name    : ConsistentSubmodular.GridStream.card_stageColumns
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-11-13T16:21:58.365323+00:00
-- url     : https://prove2.me/theorems/3917aaba-55f4-41dc-bbc7-e4419a0db43c
-- title:
--   Each stage presents exactly $k$ elements
-- statement:
--   Let $k,m,j$ be natural numbers with $j\le m$. The set of stream positions $e$ in the grid stream with $jk\le e<(j+1)k$ has exactly $k$ elements:
--   $$\bigl|\{e:\ jk\le e<(j+1)k\}\bigr|=k .$$
--
--   For $j\ge1$ these positions are the columns $b_{1,j},\dots,b_{k,j}$ of stage $j$ of the coverage stream $\Sigma$ (for $j=0$ they are the rows). The count is needed to check that the stage columns form a feasible competitor of size $k$.
-- source:
--   Balkanski, Dütting, Fusco, Lattanzi, Norouzi-Fard, Svensson, Zadimoghaddam, Consistent Submodular Maximization with Full Foresight, STOC 2027 submission; the authors' Lean formalization, https://github.com/epfl-thl2/project-consistent-submodular-full-foresight/blob/7f6a57204aa7ba76e9adf56af1d4e465368e4d8a/ConsistentSubmodular/Deterministic/Impossibility/GridStreamCoverage.lean#L270-L283 (`ConsistentSubmodular.GridStream.card_stageColumns`)

import Mathlib
import Definitions.Def_ConsistentSubmodular_Deterministic_Impossibility_GridStreamCoverage

open scoped BigOperators
open Finset
open ConsistentSubmodular ConsistentSubmodular.GridStream

theorem ConsistentSubmodular.GridStream.card_stageColumns {k m j : ℕ} (hj : j ≤ m) : (stageColumns k m j).card = k := by sorry
