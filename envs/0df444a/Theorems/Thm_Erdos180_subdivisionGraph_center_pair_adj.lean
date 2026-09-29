-- Prove2me | Theorems.Thm_Erdos180_subdivisionGraph_center_pair_adj
-- name    : Erdos180.subdivisionGraph_center_pair_adj
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:05:59.169525+00:00
-- url     : https://prove2.me/theorems/3c1122e8-0f3f-46e1-931b-808cd647cbef
-- title:
--   Centres are adjacent to their subdivision vertices
-- statement:
--   In $S_k$, the centre vertex indexed by $c$ is adjacent to the subdivision vertex indexed
--   by $(b, c)$, for every base $b$. Together with the previous lemma this is the complete
--   adjacency description of $S_k$ (Definition 2.1).
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L1862-L1867

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Basic

open Erdos180
open SimpleGraph
variable (K : Type*) [Field K]

theorem Erdos180.subdivisionGraph_center_pair_adj
    (k : ℕ) (base : Fin 3) (center : Fin k) :
    (SubdivisionGraph k).Adj
      (.inl (.inr center)) (.inr (base, center)) := by sorry
