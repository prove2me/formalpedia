-- Prove2me | Theorems.Thm_FlowAllocationGames_UnitRanking_clearing_thresholdProfile_eq
-- name    : FlowAllocationGames.UnitRanking.clearing_thresholdProfile_eq
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:40:20.170765+00:00
-- url     : https://prove2.me/theorems/2fb80316-3f40-404a-90ca-355d48df12b7
-- title:
--   Proof of Theorem 9, p. 23 — in $a^*$ the optimal circulation is the clearing state
-- statement:
--   Let $f^*$ be an optimal circulation of $G'$. Let every player $v$ choose an arbitrary permutation $\pi_v$ of $E^+(v)$ and thresholds $\tau_e = f^*_e$, and let $a^*$ be the resulting profile of threshold-ranking strategies. Then the clearing state of $a^*$ is $f^*$ restricted to the edges of $G$:
--
--   $$
--   \hat f_e(a^*) = f^*_e \qquad (e \in E).
--   $$
--
--   Combined with the upper bound of the optimal circulation, $a^*$ maximizes the total flow.
--
--   Differences from the source:
--   - encoding: an optimal (real) circulation, assumed integral → a circulation maximal among integral circulations; reason: integral capacities; clearing states of unit-ranking profiles are integral
--   - generalization: a graph G = (V, E) with a set of directed edges → edges indexed by Fin m with tail and head maps, so parallel edges and self-loops are allowed, and n = 0 or m = 0; reason: the argument is unchanged; on a simple graph the statement is the source's
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, proof of Theorem 9, p. 23, ¶4

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_clearing
import Definitions.Def_FlowAllocationGames_UnitRanking_Circ
import Definitions.Def_FlowAllocationGames_UnitRanking_IsMaxCirculation
import Definitions.Def_FlowAllocationGames_UnitRanking_thresholdProfile

namespace FlowAllocationGames.UnitRanking

/-- **The optimal circulation is the clearing state of `a∗`.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, proof of Theorem 9,
p. 23: "We choose a∗ as follows. Every firm v chooses an arbitrary permutation πv over E⁺(v) and
sets τe = f∗e. It is easy to see that in a∗, the optimal circulation f∗ corresponds to the
clearing state."

For an optimal circulation `x` in `G′` and every order `ord` listing each edge once, the clearing
state of the threshold-ranking profile with order `ord` and thresholds `τ e = flow e` is the flow
of `x` on the edges of `G`.

**Formalization Note.** The statement covers every order, as "an arbitrary permutation" says. -/
theorem clearing_thresholdProfile_eq {n m : ℕ} (Γ : Game n m) (x : Circ n m)
    (hx : IsMaxCirculation Γ x) (ord : List (Fin m)) (hord : ord.Perm (List.finRange m)) :
    clearing Γ (thresholdProfile Γ (ord, x.flow)) = x.flow := by sorry

end FlowAllocationGames.UnitRanking
