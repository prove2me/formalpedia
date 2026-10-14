-- Prove2me | Theorems.Thm_FlowAllocGames_StrongEq_optimal_circulation_bound
-- name    : FlowAllocGames.StrongEq.optimal_circulation_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:22.090069+00:00
-- url     : https://prove2.me/theorems/f8a0078f-0fce-4d68-8810-45e9bdf4663b
-- title:
--   Proof of Theorem 9, p. 23, first display — an optimal circulation saturates (s, v) and bounds 2Σb + Flow(a)
-- statement:
--   Let $f^*$ be an optimal circulation of the circulation network $G'$ of a flow allocation game, i.e. an integral circulation maximizing the total value $\sum_{e\in E'} f^*_e$ over all edges $E'$ of $G'$. Then
--
--   1. $f^*$ saturates every auxiliary edge $(s,v)$: $f^*_{(s,v)} = b_v$ for all $v \in V$;
--   2. its total value is
--   $$\sum_{e\in E'} f^*_e = 2\sum_{v\in V} b_v + \sum_{v\in V}\sum_{e\in E^+(v)} f^*_e = 2\sum_{v\in V} b_v + \mathrm{Flow}(f^*);$$
--   3. for every unit-ranking profile $\mathbf a$,
--   $$\sum_{e\in E'} f^*_e \ \ge\ 2\sum_{v\in V} b_v + \mathrm{Flow}(\mathbf a).$$
--
--   Thus the flow of an optimal circulation on the edges of $G$ is an upper bound on the total flow $\mathrm{Flow}(\mathbf a)$ achievable by any strategy profile; the proof of Theorem 9 then realizes this bound by a strong equilibrium.
--
--   **Formalization Note.** $\mathrm{Flow}(f^*) = \sum_{e\in E} f^*_e$, since every edge of $G$ has exactly one tail. Optimality is among integral circulations (see the model's note: the paper assumes $f^*$ integral by integrality of capacities).
-- source:
--   arXiv:1908.01714v3, proof of Theorem 9, p. 23, first display

import Mathlib
import Definitions.Def_FlowAllocGames_StrongEq_Model

namespace FlowAllocGames.StrongEq

open Finset

/-- Proof of Theorem 9 (arXiv:1908.01714v3, p. 23, first display): an optimal circulation `f*` of
`G′` saturates every auxiliary edge `(s, v)`, its total flow value is `2 Σ_v b_v + Flow(f*)`,
and this bounds `2 Σ_v b_v + Flow(a)` for every unit-ranking profile `a`. -/
theorem optimal_circulation_bound {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Game V E) (x : ExtFlow V E) (hx : G.IsOptimalCirculation x) :
    (∀ v, x.fromS v = G.b v) ∧ x.total = 2 * ∑ v, G.b v + ∑ e, x.g e ∧
      ∀ a : Profile E, G.IsUnitRanking a → 2 * ∑ v, G.b v + G.flow a ≤ x.total := by sorry

end FlowAllocGames.StrongEq
