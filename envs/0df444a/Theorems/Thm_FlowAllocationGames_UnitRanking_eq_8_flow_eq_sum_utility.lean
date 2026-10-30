-- Prove2me | Theorems.Thm_FlowAllocationGames_UnitRanking_eq_8_flow_eq_sum_utility
-- name    : FlowAllocationGames.UnitRanking.eq_8_flow_eq_sum_utility
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:35:26.543425+00:00
-- url     : https://prove2.me/theorems/27c8d1d8-10fa-4aa4-aff2-4e5b41a3dfba
-- title:
--   Equation (8) — total flow equals the sum of utilities
-- statement:
--   For every strategy profile $a$, with clearing state $\hat f$,
--
--   $$
--   \mathrm{Flow}(a) = \sum_{e\in E} \hat f_e = \sum_{v\in V}\sum_{e\in E^+(v)} \hat f_e = \sum_{v\in V} u_v(a).
--   $$
--
--   The total flow is the utilitarian welfare of the profile.
--
--   Differences from the source:
--   - generalization: a graph G = (V, E) with a set of directed edges → edges indexed by Fin m with tail and head maps, so parallel edges and self-loops are allowed, and n = 0 or m = 0; reason: the argument is unchanged; on a simple graph the statement is the source's
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, §2.3, p. 16, eq. (8)

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_Profile
import Definitions.Def_FlowAllocationGames_UnitRanking_utility
import Definitions.Def_FlowAllocationGames_UnitRanking_totalFlow

namespace FlowAllocationGames.UnitRanking

/-- **Equation (8).**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, eq. (8), p. 16:
"Flow(a) = Σ_{e∈E} f̂e = Σ_{v∈V} Σ_{e∈E⁺(v)} f̂e = Σ_{v∈V} uv(a)".

For every profile `a`, the total flow equals the sum of the utilities of all players. -/
theorem eq_8_flow_eq_sum_utility {n m : ℕ} (Γ : Game n m) (a : Profile m) :
    totalFlow Γ a = ∑ v, utility Γ a v := by sorry

end FlowAllocationGames.UnitRanking
