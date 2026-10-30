-- Prove2me | Theorems.Thm_FlowAllocationGames_UnitRanking_deviation_chain_step
-- name    : FlowAllocationGames.UnitRanking.deviation_chain_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:41:06.661004+00:00
-- url     : https://prove2.me/theorems/5574aa0b-8fc8-4cd1-950c-c29d4aadef15
-- title:
--   Proof of Theorem 9, pp. 23–24 — every increase has an increase upstream
-- statement:
--   Let $a$ and $a'$ be profiles of unit-ranking strategies, $C$ a coalition, $\hat f$ the clearing state of $a$ and $\hat f'$ that of $(a'_C, a_{-C})$. Let $v$ be a node such that either
--
--   1. $v \in C$ and $u_v(a'_C, a_{-C}) > u_v(a)$, or
--   2. $v \notin C$ and some outgoing edge $e$ of $v$ has $\hat f'_e > \hat f_e$.
--
--   Then some incoming edge $e = (w, v)$ of $v$ has $\hat f'_e > \hat f_e$.
--
--   In case 1 no-fraud forces more incoming flow; in case 2 the unchanged monotone strategy of $v$ forces a larger total supply. Iterated along the edges, this is the chain of the proof of Theorem 9.
--
--   Differences from the source:
--   - generalization: the argument for the profile a∗ and a profitable deviation of C → any profile a of unit-ranking strategies, any coalition C and any unit-ranking a′; reason: the argument uses only no-fraud and monotonicity; with a = a∗ it is the page's claim
--   - generalization: a graph G = (V, E) with a set of directed edges → edges indexed by Fin m with tail and head maps, so parallel edges and self-loops are allowed, and n = 0 or m = 0; reason: the argument is unchanged; on a simple graph the statement is the source's
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, proof of Theorem 9, pp. 23–24, ¶5 of p. 23 and ¶1 of p. 24

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_Profile
import Definitions.Def_FlowAllocationGames_UnitRanking_IsUnitRankingProfile
import Definitions.Def_FlowAllocationGames_UnitRanking_clearing
import Definitions.Def_FlowAllocationGames_UnitRanking_utility
import Definitions.Def_FlowAllocationGames_UnitRanking_deviate

namespace FlowAllocationGames.UnitRanking

/-- **The chain step of the proof of Theorem 9.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, proof of Theorem 9,
pp. 23–24: "Consider a node v ∈ C. Since uv(a′C, a∗−C) > uv(a∗), there must be strictly more
outgoing flow from v in the new profile. Due to the no-fraud condition, this can only happen if v
also has strictly more incoming flow in the new profile. Hence, there is an incoming edge
e = (w, v) ∈ E⁻(v) with f̂′e > f∗e. Now consider node w. If w ∈ C, then uw(a′C, a∗−C) > uw(a∗), so
by the same reasoning there is again some incoming edge in E⁻(w) that has strictly more flow in
f̂′. Otherwise, if w ∉ C, then w still plays the strategy a∗w. Due to monotonicity, a higher flow
on (w, v) can only occur if w has larger total supply. Thus, there is again some incoming edge in
E⁻(w) that has strictly more flow in f̂′."

Let `a` and `a'` be profiles of unit-ranking strategies, `C` a coalition, `f` the clearing state of
`a` and `f'` that of the deviation `(a′C, a−C)`. If a node `v` either belongs to `C` and strictly
gains utility, or does not belong to `C` and has an outgoing edge with strictly more flow in `f'`
than in `f`, then some incoming edge of `v` has strictly more flow in `f'` than in `f`.

**Formalization Note.** The page argues for `a = a∗`; the argument uses only that `a` is a
profile of unit-ranking strategies (no-fraud and monotonicity), so the statement is made for every
such `a` (a generalization that specializes to the page's claim). -/
theorem deviation_chain_step {n m : ℕ} (Γ : Game n m) (a a' : Profile m)
    (ha : IsUnitRankingProfile Γ a) (ha' : IsUnitRankingProfile Γ a') (C : Finset (Fin n))
    (v : Fin n)
    (hv : (v ∈ C ∧ utility Γ a v < utility Γ (deviate Γ a C a') v) ∨
      (v ∉ C ∧ ∃ e, Γ.tail e = v ∧ clearing Γ a e < clearing Γ (deviate Γ a C a') e)) :
    ∃ e, Γ.head e = v ∧ clearing Γ a e < clearing Γ (deviate Γ a C a') e := by sorry

end FlowAllocationGames.UnitRanking
