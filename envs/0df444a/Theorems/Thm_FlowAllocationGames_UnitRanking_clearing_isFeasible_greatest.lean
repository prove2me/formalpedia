-- Prove2me | Theorems.Thm_FlowAllocationGames_UnitRanking_clearing_isFeasible_greatest
-- name    : FlowAllocationGames.UnitRanking.clearing_isFeasible_greatest
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:33:58.082442+00:00
-- url     : https://prove2.me/theorems/cf228b88-7ebe-4dfe-85f5-b1f972646650
-- title:
--   The clearing state is the greatest feasible flow (integral model, p. 13)
-- statement:
--   Let $a$ be a profile of monotone integral strategies, and let $\hat f$ be the coordinatewise supremum of its feasible flows. Then
--
--   1. $\hat f$ is itself a feasible flow, and
--   2. every feasible flow $f$ satisfies $f \le \hat f$ coordinatewise.
--
--   So $\hat f$ is the supremum of the lattice of feasible flows and the unique feasible flow of maximum total flow, the clearing state of the paper; the utilities $u_v(a)$ and the total flow $\mathrm{Flow}(a)$ are computed from it.
--
--   Differences from the source:
--   - reading: "the supremum of the lattice … the unique feasible flow that maximizes the total flow in the network" → the coordinatewise supremum of the feasible flows is feasible and above every feasible flow; reason: a greatest feasible flow is the supremum of the lattice and the unique maximizer of the total flow
--   - reading: strategies a_e : ℝ≥0 → ℝ≥0 and real flows (§2.1) → integral strategies ℕ → ℕ and integral flows; reason: p. 13 states that Theorem 2 also holds for a_e : N0 → N0 ("This ensures that unit-ranking strategies are well-defined in our model"), so the clearing state of the integral model is the paper's own object; it is the one Theorem 9 uses
--   - generalization: a graph G = (V, E) with a set of directed edges → edges indexed by Fin m with tail and head maps, so parallel edges and self-loops are allowed, and n = 0 or m = 0; reason: the argument is unchanged; on a simple graph the statement is the source's
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, §2.1, p. 13

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_Profile
import Definitions.Def_FlowAllocationGames_UnitRanking_IsMonotoneProfile
import Definitions.Def_FlowAllocationGames_UnitRanking_IsFeasible
import Definitions.Def_FlowAllocationGames_UnitRanking_clearing

namespace FlowAllocationGames.UnitRanking

/-- **The clearing state is the greatest feasible flow.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, §2.1, p. 13: "we
concentrate on the supremum of the lattice. For every profile a, we focus on the unique feasible
flow that maximizes the total flow in the network. We denote this feasible flow by f̂ and call it
the clearing state of strategy profile a."

For a profile `a` of monotone strategies, `clearing Γ a` is a feasible flow and every feasible
flow is coordinatewise at most `clearing Γ a`.

**Formalization Note.** This makes `clearing`, and with it `utility` and `totalFlow`, the paper's
`f̂`, `uv(a)` and `Flow(a)`. -/
theorem clearing_isFeasible_greatest {n m : ℕ} (Γ : Game n m) (a : Profile m)
    (ha : IsMonotoneProfile Γ a) :
    IsFeasible Γ a (clearing Γ a) ∧ ∀ f, IsFeasible Γ a f → f ≤ clearing Γ a := by sorry

end FlowAllocationGames.UnitRanking
