-- Prove2me | Theorems.Thm_Erdos146_pairGraphOverFin_connected
-- name    : Erdos146.pairGraphOverFin_connected
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T04:44:17.683532+00:00
-- url     : https://prove2.me/theorems/1dcee639-8560-4e83-87b1-38d91c2cad2c
-- title:
--   The layered graph is connected (Fact 6.1)
-- statement:
--   **Fact 6.1, connectivity.** The layered graph $H$ is connected. The counterexample graph $H$ is built in layers (Section 6): starting from a layer $V_0$ of size $L_0$, each subsequent layer is $V_i = \binom{V_{i-1}}{2}$, and every vertex $\{a,b\} \in V_i$ is joined to its two parents $a, b \in V_{i-1}$. Fact 6.1 records that the result is connected, bipartite and 2-degenerate.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L12262-L12266

import Definitions.Def_erdos146_core2
import Mathlib.AlgebraicTopology.SimplexCategory.Basic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

open Erdos146
open Filter Finset SimpleGraph
open scoped Topology

theorem Erdos146.pairGraphOverFin_connected (baseSize depth : ℕ)
    (hbase : 0 < baseSize) (hdepth : 0 < depth) :
    (pairGraphOverFin baseSize depth).Connected := by sorry
