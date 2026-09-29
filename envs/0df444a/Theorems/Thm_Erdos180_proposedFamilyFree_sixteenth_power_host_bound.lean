-- Prove2me | Theorems.Thm_Erdos180_proposedFamilyFree_sixteenth_power_host_bound
-- name    : Erdos180.proposedFamilyFree_sixteenth_power_host_bound
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:20:13.099447+00:00
-- url     : https://prove2.me/theorems/39c640cf-26e4-419f-8837-27259b4a5797
-- title:
--   The sixteenth-power edge bound
-- statement:
--   Every $\mathcal{F}$-free graph on $n$ vertices satisfies
--
--   $$e(G)^{16} \;\le\; C_2\, n^{21} ,$$
--
--   that is, $e(G) = O\big(n^{21/16}\big)$.
--
--   This is Proposition 3.4 of the source, $\mathrm{ex}(n,\mathcal{F}) = O(n^{21/16}) =
--   O(n^{4/3 - 1/48})$, in polynomial form. Lemma 3.3 gives a bipartite subgraph with
--   $d \ge m/(2n)$ and $\Delta(B)(d-1)^2 \le N$; feeding $d$ into the sixteenth-power degree bound
--   and clearing denominators produces the displayed inequality with an explicit constant.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L8811-L8854

import Definitions.Def_erdos180_core4
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Combinatorics.SimpleGraph.Bipartite

open Erdos180
open Filter Finset SimpleGraph
open scoped Classical Topology

theorem Erdos180.proposedFamilyFree_sixteenth_power_host_bound
    (n : ℕ) (host : SimpleGraph (Fin n))
    (hfree : FamilyFree proposedFamily host) :
    (host.edgeFinset.card : ℝ) ^ 16 ≤
      compactnessHostPowerConstant * (n : ℝ) ^ 21 := by sorry
