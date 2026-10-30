-- Prove2me | Theorems.Thm_FlowAllocationGames_UnitRanking_theorem_9_optimal_strong_equilibrium
-- name    : FlowAllocationGames.UnitRanking.theorem_9_optimal_strong_equilibrium
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:42:58.361998+00:00
-- url     : https://prove2.me/theorems/c9a0b697-6666-4873-9aa6-bfe1ac458f22
-- title:
--   Theorem 9 — a flow-maximizing strong equilibrium, computable in polynomial time, representable in polynomial space
-- statement:
--   For every unit-ranking game there is a strong equilibrium that maximizes the total amount of flow; it can be computed in polynomial time, and the equilibrium profile can be represented in polynomial space.
--
--   Precisely: there are constants $C$ and $k$ such that for every flow allocation game $\Gamma$ with $n$ players and $m$ edges, the algorithm $\mathsf{computeSE}$, run from zero counters, outputs threshold-ranking data $R$ such that
--
--   1. $R$ is valid (every edge listed once, thresholds at most the capacities);
--   2. the profile $a^*$ of threshold-ranking strategies described by $R$ is a strong equilibrium: no nonempty coalition has a unit-ranking deviation that strictly improves the utility of all its members;
--   3. $a^*$ maximizes the total flow: $\mathrm{Flow}(a) \le \mathrm{Flow}(a^*)$ for every profile $a$ of unit-ranking strategies;
--   4. the run has bit cost at most $C\,(\operatorname{inputSize}(\Gamma) + 1)^k$;
--   5. the run has at most $C\,(n + m + 1)^k$ steps;
--   6. the representation has size $\operatorname{reprSize}(R) \le C\,(\operatorname{inputSize}(\Gamma) + 1)^k$.
--
--   In particular the price of stability of strong equilibria for the total flow is $1$ in every unit-ranking game.
--
--   Differences from the source:
--   - reading: "can be computed in polynomial time" (strongly polynomial on pp. 5 and 39) → a fixed algorithm with bit cost ≤ C·(inputSize + 1)^k and step count ≤ C·(n + m + 1)^k in the tick model, with C, k independent of the game; reason: the paper fixes no machine model; the two counters give the literal claim and the strongly polynomial one
--   - reading: "no coalition C ⊆ V has any profitable deviation" → no nonempty coalition; reason: for C = ∅ "strictly better for every player in C" holds vacuously, so the literal reading admits no strong equilibrium
--   - reading: unit-ranking strategies (rankings of particles, p. 14) → integral strategies ℕ → ℕ with the capacity, weak conservation, no-fraud and monotonicity constraints; reason: under no-fraud and monotonicity integral strategies are exactly rankings of units
--   - encoding: "there is a strong equilibrium … can be computed … can be represented in polynomial space" → the output R of computeSE decodes through thresholdProfile to the equilibrium and has polynomial reprSize; reason: an explicit algorithm and representation witness existence, computability and space
--   - encoding: "maximizes the total amount of flow" → Flow(a) ≤ Flow(a∗) for every profile a of unit-ranking strategies; reason: the maximum is over the game's strategy space
--   - generalization: a graph G = (V, E) with a set of directed edges → edges indexed by Fin m with tail and head maps, so parallel edges and self-loops are allowed, and n = 0 or m = 0; reason: the argument is unchanged; on a simple graph the statement is the source's
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, Theorem 9, pp. 22–23 (proof pp. 23–24)

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_Profile
import Definitions.Def_FlowAllocationGames_UnitRanking_IsUnitRankingProfile
import Definitions.Def_FlowAllocationGames_UnitRanking_totalFlow
import Definitions.Def_FlowAllocationGames_UnitRanking_IsStrongEquilibrium
import Definitions.Def_FlowAllocationGames_UnitRanking_IsValidThreshold
import Definitions.Def_FlowAllocationGames_UnitRanking_thresholdProfile
import Definitions.Def_FlowAllocationGames_UnitRanking_inputSize
import Definitions.Def_FlowAllocationGames_UnitRanking_reprSize
import Definitions.Def_FlowAllocationGames_UnitRanking_computeSE

namespace FlowAllocationGames.UnitRanking

/-- **Theorem 9.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, Theorem 9,
pp. 22–23: "For every unit-ranking game, there is a strong equilibrium that maximizes the total
amount of flow. The strong equilibrium can be computed in polynomial time, and the equilibrium
profile can be represented in polynomial space."

There are constants `C, k` such that for every game `Γ` with `n` players and `m` edges, the run of
`computeSE Γ` from the zero counters returns threshold-ranking data `R` such that
1. `R` is valid;
2. the profile `a∗ = thresholdProfile Γ R` is a strong equilibrium;
3. `a∗` maximizes the total flow over all profiles of unit-ranking strategies;
4. the run costs at most `C · (inputSize Γ + 1)^k` bits;
5. the run takes at most `C · (n + m + 1)^k` steps;
6. the representation `R` has size at most `C · (inputSize Γ + 1)^k`.

**Formalization Note.** Reading 1: "polynomial time" is read in the tick model with both counters
(the strongly polynomial claim of pp. 5 and 39 is clause 5). Reading 3: strong equilibria exclude
the empty coalition (`IsStrongEquilibrium`). Reading 5: "can be computed" is witnessed by
`computeSE`, and "can be represented in polynomial space" by `R`, which decodes to the equilibrium
through `thresholdProfile` and has polynomial size. Reading 6: parallel edges and self-loops are
allowed, and `n = 0` or `m = 0`. `C` and `k` are chosen before `n`, `m` and `Γ`. -/
theorem theorem_9_optimal_strong_equilibrium :
    ∃ C k : ℕ, ∀ {n m : ℕ} (Γ : Game n m),
      IsValidThreshold Γ ((computeSE Γ).run ⟨0, 0⟩).1 ∧
      IsStrongEquilibrium Γ (thresholdProfile Γ ((computeSE Γ).run ⟨0, 0⟩).1) ∧
      (∀ a : Profile m, IsUnitRankingProfile Γ a →
        totalFlow Γ a ≤ totalFlow Γ (thresholdProfile Γ ((computeSE Γ).run ⟨0, 0⟩).1)) ∧
      ((computeSE Γ).run ⟨0, 0⟩).2.bits ≤ C * (inputSize Γ + 1) ^ k ∧
      ((computeSE Γ).run ⟨0, 0⟩).2.ops ≤ C * (n + m + 1) ^ k ∧
      reprSize ((computeSE Γ).run ⟨0, 0⟩).1 ≤ C * (inputSize Γ + 1) ^ k := by sorry

end FlowAllocationGames.UnitRanking
