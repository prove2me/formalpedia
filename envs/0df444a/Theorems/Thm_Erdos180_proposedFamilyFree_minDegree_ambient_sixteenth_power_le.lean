-- Prove2me | Theorems.Thm_Erdos180_proposedFamilyFree_minDegree_ambient_sixteenth_power_le
-- name    : Erdos180.proposedFamilyFree_minDegree_ambient_sixteenth_power_le
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:19:52.445934+00:00
-- url     : https://prove2.me/theorems/3b61be59-9cbd-455d-96d8-938a2020d379
-- title:
--   The degree bound relative to an ambient order
-- statement:
--   If an $\mathcal{F}$-free bipartite graph of order $N \le n$ has minimum degree $d$, then
--
--   $$d^{16} \;\le\; C_1\, n^5 .$$
--
--   Lemma 3.3 of the source produces its bipartite subgraph $B$ on $N \le n$ vertices from a graph
--   on $n$ vertices, so the degree bound of Proposition 3.4 must be re-expressed against the ambient
--   order $n$ before it can be combined with $m \le 2nd$.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L8750-L8806

import Definitions.Def_erdos180_core4
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite

open Erdos180
open Filter Finset SimpleGraph
open scoped Classical Topology

theorem Erdos180.proposedFamilyFree_minDegree_ambient_sixteenth_power_le
    {N n : ℕ} (host : SimpleGraph (Fin N))
    (hN : 0 < N) (hn : 0 < n) (hNn : N ≤ n)
    (hfree : FamilyFree proposedFamily host)
    (hbip : host.IsBipartite)
    (d : ℕ) (hdegree : ∀ v : Fin N, d ≤ host.degree v) :
    (d : ℝ) ^ 16 ≤
      compactnessDegreePowerConstant * (n : ℝ) ^ 5 := by sorry
