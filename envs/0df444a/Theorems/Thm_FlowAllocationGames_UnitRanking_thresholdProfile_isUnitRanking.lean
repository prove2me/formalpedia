-- Prove2me | Theorems.Thm_FlowAllocationGames_UnitRanking_thresholdProfile_isUnitRanking
-- name    : FlowAllocationGames.UnitRanking.thresholdProfile_isUnitRanking
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:39:24.105055+00:00
-- url     : https://prove2.me/theorems/3c32a8c9-d3b0-4efc-9f41-309130d21ee6
-- title:
--   Proof of Theorem 9, p. 23 — threshold-ranking strategies are compact unit-ranking strategies and generalize edge-ranking strategies
-- statement:
--   1. Let $(\mathrm{ord}, \tau)$ be valid threshold-ranking data: $\mathrm{ord}$ lists every edge once and $\tau_e \le c_e$. The profile of threshold-ranking strategies (each node $v$ first assigns $\tau_e$ units to each $e\in E^+(v)$ in the order $\pi_v$, the restriction of $\mathrm{ord}$ to $E^+(v)$, then the remaining $c_e - \tau_e$ units in the same order) consists of unit-ranking strategies: capacity, weak flow conservation, no-fraud and monotonicity hold. Its representation is compact:
--   $$
--   \operatorname{reprSize}(\mathrm{ord}, \tau) \le (\operatorname{inputSize}(\Gamma) + 1)^2 .
--   $$
--   2. Threshold-ranking strategies are more general than edge-ranking strategies: for every order $\mathrm{ord}$ listing each edge once, the threshold-ranking profile with thresholds $\tau = 0$ is the edge-ranking profile of p. 14,
--   $$
--   a_{e_i}(y) = \min\Bigl\{c_{e_i}, \max\bigl\{0,\ y - \textstyle\sum_{j<i} c_{e_j}\bigr\}\Bigr\},
--   $$
--   where $e_1, e_2, \dots$ are the edges of $E^+(v)$ in the order $\mathrm{ord}$.
--
--   This is what lets the strong equilibrium of Theorem 9 be written down in polynomial space.
--
--   Differences from the source:
--   - reading: "a special class of unit-ranking strategies with compact representation" → unit-ranking, and reprSize ≤ (inputSize + 1)²; reason: "compact" is made explicit with the bound of the obvious count of bits
--   - reading: "threshold-ranking strategies are more general than edge-ranking strategies" → for every order, the threshold-ranking profile with τ = 0 equals the edge-ranking profile a_{e_i}(y) = min{c_{e_i}, max{0, y − Σ_{j<i} c_{e_j}}} of p. 14; reason: "more general" is read as inclusion: every edge-ranking strategy is a threshold-ranking strategy
--   - encoding: a permutation πv over E⁺(v) for every v → one global order of the edges, restricted to E⁺(v); reason: every family of permutations arises this way, and conversely
--   - generalization: a graph G = (V, E) with a set of directed edges → edges indexed by Fin m with tail and head maps, so parallel edges and self-loops are allowed, and n = 0 or m = 0; reason: the argument is unchanged; on a simple graph the statement is the source's
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, proof of Theorem 9, p. 23, ¶3

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_IsUnitRankingProfile
import Definitions.Def_FlowAllocationGames_UnitRanking_ThresholdRanking
import Definitions.Def_FlowAllocationGames_UnitRanking_IsValidThreshold
import Definitions.Def_FlowAllocationGames_UnitRanking_thresholdProfile
import Definitions.Def_FlowAllocationGames_UnitRanking_inputSize
import Definitions.Def_FlowAllocationGames_UnitRanking_reprSize

namespace FlowAllocationGames.UnitRanking

/-- **Threshold-ranking strategies are unit-ranking strategies, and generalize edge-ranking ones.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, proof of Theorem 9,
p. 23: "In a threshold-ranking strategy, every firm v chooses a permutation πv over E⁺(v) and
thresholds τe. … Clearly, threshold-ranking strategies are more general than edge-ranking
strategies. They constitute a special class of unit-ranking strategies with compact
representation." Edge-ranking strategies, §2.2, p. 14: for `πv = (e1, e2, …)`,
"aei(y) = min{cei, max{0, y − Σ_{j<i} cej}}".

1. For valid threshold-ranking data `R = (ord, τ)` (every edge listed once, `τ e ≤ c e`), the
   profile `thresholdProfile Γ R` consists of unit-ranking strategies, and its representation is
   compact: `reprSize R ≤ (inputSize Γ + 1)²`.
2. Every edge-ranking profile is a threshold-ranking profile: for every order `ord` listing each
   edge once, the threshold-ranking profile with order `ord` and thresholds `τ = 0` is the
   edge-ranking profile of p. 14 with `πv` the restriction of `ord` to `E⁺(v)`.

**Formalization Note.** Clause 1's bound makes "with compact representation" explicit, with the
constant of the obvious count (`m` edge indices of `size m + 1` bits and thresholds `τ e ≤ c e`).
Clause 2 reads "more general than edge-ranking strategies" as inclusion. In clause 2, `ℕ`'s
truncated subtraction is the page's `max{0, ·}`, and the edges before `e` in `πv` are those before
`e` in the filtered order. -/
theorem thresholdProfile_isUnitRanking {n m : ℕ} (Γ : Game n m) :
    (∀ R : ThresholdRanking m, IsValidThreshold Γ R →
      IsUnitRankingProfile Γ (thresholdProfile Γ R) ∧
      reprSize R ≤ (inputSize Γ + 1) ^ 2) ∧
    ∀ ord : List (Fin m), ord.Perm (List.finRange m) → ∀ (e : Fin m) (y : ℕ),
      thresholdProfile Γ (ord, fun _ => 0) e y =
        min (Γ.c e) (y - (((ord.filter (fun x => decide (Γ.tail x = Γ.tail e))).take
          ((ord.filter (fun x => decide (Γ.tail x = Γ.tail e))).idxOf e)).map Γ.c).sum) := by sorry

end FlowAllocationGames.UnitRanking
