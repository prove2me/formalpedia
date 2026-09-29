-- Prove2me | Theorems.Thm_ChvatalPolytopes_SeriesParallel_deleteIdentify_isSeriesParallel
-- name    : ChvatalPolytopes.SeriesParallel.deleteIdentify_isSeriesParallel
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-26T20:26:02.234867+00:00
-- url     : https://prove2.me/theorems/245ced53-a3af-44c5-98c9-754e3fb153de
-- title:
--   Case 4: deleting a degree-two vertex and identifying its neighbours keeps a series-parallel network
-- statement:
--   Let $G=(V,E)$ be a finite series-parallel network and let $u$ be a vertex of degree $d(u)=2$ whose two neighbours $v\ne w$ are not adjacent. Delete $u$ and identify $v$ and $w$; call the resulting graph $G'$ (vertex set $V\setminus\{u,w\}$, the vertex $v$ standing for $v\equiv w$). Then
--   $$
--   G'\ \text{is again a series-parallel network.}
--   $$
--
--   This closure property is the step that makes the induction in the proof of Theorem 7.1 go through in its hardest case.
--
--   **Formalization Note** $G'$ is `deleteIdentify G u v w`. "The two neighbours of $u$ are $v,w$" is encoded by $uv,uw\in E$, $v\ne w$ and $d(u)=2$.
-- source:
--   Chvátal, On certain polytopes associated with graphs, J. Combin. Theory Ser. B 18 (1975), p. 151, proof of Theorem 7.1, Case 4

import Mathlib
import Definitions.Def_ChvatalPolytopes_SeriesParallel_IsSeriesParallel
import Definitions.Def_ChvatalPolytopes_SeriesParallel_deleteIdentify

namespace ChvatalPolytopes.SeriesParallel

/-- Chvátal 1975, p. 151, proof of Theorem 7.1, Case 4: let `u` be a vertex of degree two whose
two neighbours `v`, `w` are not adjacent. Delete `u` and identify its neighbours `v`, `w`. The
resulting graph `G'` is again a series-parallel network. -/
theorem deleteIdentify_isSeriesParallel {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (hG : IsSeriesParallel G)
    (u v w : V) (hvw : v ≠ w) (huv : G.Adj u v) (huw : G.Adj u w)
    (hdeg : G.degree u = 2) (hnadj : ¬ G.Adj v w) :
    IsSeriesParallel (deleteIdentify G u v w) := by sorry

end ChvatalPolytopes.SeriesParallel
