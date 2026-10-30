-- Prove2me | Theorems.Thm_FlowAllocationGames_UnitRanking_maxCirc_spec
-- name    : FlowAllocationGames.UnitRanking.maxCirc_spec
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-30T00:38:31.142804+00:00
-- url     : https://prove2.me/theorems/bbf19a18-c7fd-475f-83f7-bef9de1b093f
-- title:
--   Proof of Theorem 9, p. 23 — $f^*$ can be computed in strongly polynomial time
-- statement:
--   There are constants $C$ and $k$ such that for every flow allocation game $\Gamma$ with $n$ nodes and $m$ edges, the algorithm $\mathsf{maxCirc}$ (minimum-mean-cycle cancelling on $G'$, started from zero counters) returns an optimal integral circulation of $G'$, and its run has
--
--   1. bit cost at most $C\,(\operatorname{inputSize}(\Gamma) + 1)^k$, and
--   2. at most $C\,(n + m + 1)^k$ steps.
--
--   The constants do not depend on the game. The step bound in $n + m$ alone is the strongly polynomial claim.
--
--   Differences from the source:
--   - reading: f∗ can be computed in strongly polynomial time [45] → a fixed algorithm (minimum-mean-cycle cancelling with Karp's algorithm) returns an optimal circulation, with bit cost polynomial in the input size and step count polynomial in n + m in the tick model; reason: the paper cites Tardos [45] and fixes neither algorithm nor machine model; a fixed algorithm with explicit counters witnesses the claim
--   - encoding: an optimal circulation, assumed integral → a circulation maximal among integral circulations; reason: integral capacities; the algorithm returns an integral optimum
--   - generalization: a graph G = (V, E) with a set of directed edges → edges indexed by Fin m with tail and head maps, so parallel edges and self-loops are allowed, and n = 0 or m = 0; reason: the argument is unchanged; on a simple graph the statement is the source's
-- source:
--   Bertschinger, Hoefer, Schmand, Flow Allocation Games, arXiv:1908.01714v3, proof of Theorem 9, p. 23 ("f∗ can be computed in strongly polynomial time [45]")

import Mathlib
import Definitions.Def_FlowAllocationGames_UnitRanking_Game
import Definitions.Def_FlowAllocationGames_UnitRanking_IsMaxCirculation
import Definitions.Def_FlowAllocationGames_UnitRanking_inputSize
import Definitions.Def_FlowAllocationGames_UnitRanking_maxCirc

namespace FlowAllocationGames.UnitRanking

/-- **`f∗` can be computed in strongly polynomial time.**
Bertschinger, Hoefer, Schmand, *Flow Allocation Games*, arXiv:1908.01714v3, proof of Theorem 9,
p. 23: "f∗ can be computed in strongly polynomial time [45]. Since all edge capacities are
integral, we can assume all f∗e are integral."

There are constants `C, k` such that for every game `Γ` with `n` players and `m` edges, the run of
`maxCirc Γ` from the zero counters returns an optimal (integral) circulation of `G′`, with bit
cost at most `C · (inputSize Γ + 1)^k` and at most `C · (n + m + 1)^k` steps.

**Formalization Note.** The paper delegates this step to Tardos [45]; the algorithm (minimum-mean-
cycle cancelling with Karp's algorithm, budget `maxCircFuel`) is the mission's choice (Reading 5).
"Strongly polynomial" is read as the step bound in `n + m` alone, next to the bit bound in the
input size (Reading 1). `C` and `k` are chosen before `n`, `m` and `Γ`. -/
theorem maxCirc_spec :
    ∃ C k : ℕ, ∀ {n m : ℕ} (Γ : Game n m),
      IsMaxCirculation Γ ((maxCirc Γ).run ⟨0, 0⟩).1 ∧
      ((maxCirc Γ).run ⟨0, 0⟩).2.bits ≤ C * (inputSize Γ + 1) ^ k ∧
      ((maxCirc Γ).run ⟨0, 0⟩).2.ops ≤ C * (n + m + 1) ^ k := by sorry

end FlowAllocationGames.UnitRanking
