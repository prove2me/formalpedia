-- Prove2me | Theorems.Thm_Erdos180_cycleGraph_no_isolated
-- name    : Erdos180.cycleGraph_no_isolated
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:08:46.242283+00:00
-- url     : https://prove2.me/theorems/0036bee8-c1ed-45df-b8be-3b5923e2c7fc
-- title:
--   Cycles have no isolated vertex
-- statement:
--   Every vertex of $C_{k+2}$ has a neighbour.
--
--   Proposition 4.3 of the source pads the incidence graph $I_q$ with isolated vertices to reach
--   an arbitrary order $n$. Padding preserves $F$-freeness precisely because every member of
--   $\mathcal{F}$ is connected and contains an edge, so it cannot embed using a padded vertex.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L2711-L2720

import Definitions.Def_erdos180_core4
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Combinatorics.SimpleGraph.Circulant

open Erdos180
open SimpleGraph

theorem Erdos180.cycleGraph_no_isolated (k : ℕ) :
    ∀ u : Fin (k + 2),
      ∃ v : Fin (k + 2),
        (SimpleGraph.cycleGraph (k + 2)).Adj u v := by sorry
