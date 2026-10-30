-- Prove2me | Theorems.Thm_FlowAllocationGames_UnitRanking_max_circulation_upper_bound
-- name    : FlowAllocationGames.UnitRanking.max_circulation_upper_bound
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:36:41.396779+00:00
-- url     : https://prove2.me/theorems/bf8136cc-5dd5-4337-94d2-28a5e2389070
-- title:
--   Proof of Theorem 9, p. 23 — an optimal circulation bounds the total flow of every profile
-- statement:
--   Let $f^*$ be an optimal (integral) circulation of $G'$, one that maximizes the sum of flow on all edges. Then
--
--   1. $f^*$ saturates all auxiliary edges out of $s$: $f^*_{(s,v)} = b_v$ for every node $v$;
--   2. its total flow value is
--   $$
--   \sum_{e\in E'} f^*_e = 2\sum_{v\in V} b_v + \sum_{v\in V}\sum_{e\in E^+(v)} f^*_e ;
--   $$
--   3. every profile $a$ of unit-ranking strategies has $\mathrm{Flow}(a) \le \sum_{e \in E} f^*_e = \mathrm{Flow}(f^*)$.
--
--   This is the upper bound against which the strong equilibrium of Theorem 9 is optimal.
--
--   Differences from the source:
--   - encoding: an optimal (real) circulation, assumed integral → a circulation maximal among integral circulations; reason: Flow(a) is integral for unit-ranking profiles, so the comparison only involves integral circulations
--   - generalization: a graph G = (V, E) with a set of directed edges → edges indexed by Fin m with tail and head maps, so parallel edges and self-loops are allowed, and n = 0 or m = 0; reason: the argument is unchanged; on a simple graph the statement is the source's
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, proof of Theorem 9, p. 23, ¶1 and display

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_Profile
import Definitions.Def_FlowAllocationGames_UnitRanking_IsUnitRankingProfile
import Definitions.Def_FlowAllocationGames_UnitRanking_totalFlow
import Definitions.Def_FlowAllocationGames_UnitRanking_Circ
import Definitions.Def_FlowAllocationGames_UnitRanking_circValue
import Definitions.Def_FlowAllocationGames_UnitRanking_IsMaxCirculation

namespace FlowAllocationGames.UnitRanking

/-- **An optimal circulation bounds the total flow of every profile.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, proof of Theorem 9,
p. 23: "Consider an optimal circulation f∗ that maximizes the total flow value, i.e., it maximizes
the sum of flow on all edges. This implies, in particular, that it saturates all outgoing auxiliary
edges from s. Clearly, f∗ yields an upper bound on the achievable total amount of flow (denoted by
Flow(f∗)) in any strategy profile a of the game Σ_{e∈E′} f∗e = 2 Σ_{v∈V} bv + Σ_{v∈V}
Σ_{e∈E⁺(v)} f∗e = 2 Σ_{v∈V} bv + Flow(f∗) ≥ 2 Σ_{v∈V} bv + Flow(a)."

For an optimal circulation `x` in `G′`:
1. every edge `(s, v)` is saturated, `fromS v = b v`;
2. the total flow value is `2 Σ_v b v + Σ_e flow e`;
3. every profile `a` of unit-ranking strategies has total flow at most `Σ_e flow e`.

**Formalization Note.** `Flow(a)` is `totalFlow Γ a`, the total flow of the clearing state;
the profiles range over the strategy space of the unit-ranking game. -/
theorem max_circulation_upper_bound {n m : ℕ} (Γ : Game n m) (x : Circ n m)
    (hx : IsMaxCirculation Γ x) :
    (∀ v, x.fromS v = Γ.b v) ∧
    circValue x = 2 * ∑ v, Γ.b v + ∑ e, x.flow e ∧
    ∀ a : Profile m, IsUnitRankingProfile Γ a → totalFlow Γ a ≤ ∑ e, x.flow e := by sorry

end FlowAllocationGames.UnitRanking
