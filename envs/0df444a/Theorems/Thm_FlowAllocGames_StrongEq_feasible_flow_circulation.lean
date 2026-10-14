-- Prove2me | Theorems.Thm_FlowAllocGames_StrongEq_feasible_flow_circulation
-- name    : FlowAllocGames.StrongEq.feasible_flow_circulation
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T03:07:26.680517+00:00
-- url     : https://prove2.me/theorems/59e78342-9cff-473e-b561-8e15670192fb
-- title:
--   Proposition 5, p. 17 — a feasible flow extends to a circulation of G′ in which s receives the total fixed supply
-- statement:
--   Let $\mathbf a$ be a unit-ranking profile of a flow allocation game and $\mathbf f$ an integral flow feasible for $\mathbf a$, with total supplies $f_v = b_v + \sum_{e\in E^-(v)} f_e$. Extend $\mathbf f$ to the circulation network $G'$ by putting the *non-forwarded flow* $\max\{0, f_v - c^+_v\}$ on the auxiliary edge $(v,s)$ and $b_v$ on the auxiliary edge $(s,v)$, for every $v\in V$. Then this extended flow is a circulation of $G'$ (capacities respected, flow conserved at every node of $V$ and at $s$), all edges $(s,v)$ are saturated, and the flow into $s$ is the total fixed supply:
--
--   $$\sum_{v\in V} \max\{0, f_v - c^+_v\} = \sum_{v\in V} b_v.$$
--
--   This circulation representation of feasible flows is the bridge between the strategic game and classical network flows on which the analysis of strong equilibria rests.
--
--   **Formalization Note.** The value on $(v,s)$ is written with truncated subtraction in $\mathbb N$, $f_v - c^+_v$, which is exactly $\max\{0, f_v - c^+_v\}$. The page's "the corresponding flow for the modified strategy profile $\mathbf a'$" is rendered by this explicit extension, which is the one the proof on p. 18 constructs. Monotonicity (5) of $\mathbf a$ is part of the unit-ranking hypothesis but not needed.
-- source:
--   arXiv:1908.01714v3, Proposition 5, p. 17, and the display of its proof, p. 18

import Mathlib
import Definitions.Def_FlowAllocGames_StrongEq_Model

namespace FlowAllocGames.StrongEq

open Finset

/-- Proposition 5 (arXiv:1908.01714v3, p. 17) with the display of its proof (p. 18): a feasible
flow `f` of a unit-ranking profile, extended by the non-forwarded flow `max{0, f_v − c⁺_v}` on
`(v, s)` and by `b_v` on `(s, v)`, is a circulation of `G′`, and the flow into `s` is
`Σ_v b_v`. -/
theorem feasible_flow_circulation {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (G : Game V E) (a : Profile E) (ha : G.IsUnitRanking a) (f : E → ℕ)
    (hf : G.IsFeasible a f) :
    G.IsCirculation ⟨f, fun v => G.supply f v - G.cplus v, G.b⟩ ∧
      ∑ v, (G.supply f v - G.cplus v) = ∑ v, G.b v := by sorry

end FlowAllocGames.StrongEq
