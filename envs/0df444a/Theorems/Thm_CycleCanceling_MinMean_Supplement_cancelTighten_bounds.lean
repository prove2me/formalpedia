-- Prove2me | Theorems.Thm_CycleCanceling_MinMean_Supplement_cancelTighten_bounds
-- name    : CycleCanceling.MinMean.Supplement.cancelTighten_bounds
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:25:09.151279+00:00
-- url     : https://prove2.me/theorems/ae35695e-3b00-4ca5-920c-cd5072f0ec63
-- title:
--   Theorem 4.1 — cancellations per phase and integer-cost phase bound
-- statement:
--   Let $N$ be a finite symmetric network with $m=|E|\ge n=|V|\ge2$ and arbitrary real capacities. Both conclusions below hold.
--
--   1. For arbitrary real costs, every $K$-step admissible-cancellation prefix at any fixed prices, from any circulation, satisfies
--
--   $$K\le m.$$
--
--   2. If the arc costs are integers, let $C$ be any natural upper bound on their absolute values. Every $T$-phase prefix of cancel-and-tighten, starting from any circulation with zero prices and counting complete Steps 1 and 2, satisfies
--
--   $$\begin{cases}T=0,&C=0,\\ T\le n\ln(nC)+1,&C>0.\end{cases}$$
--
--   The first conclusion bounds each invocation of Step 1 and has no integer-cost or zero-initial-price assumption. The paper prints $O(n\log(nC))$ for the second conclusion; its proof gives the explicit bound above. All admissible cycles and all valid tightening prices are included.
--
--   **Formalization Note** At each phase, tightening compares the new error with the error immediately after Step 1 at the old prices. A phase starts only at a nonoptimal circulation. For $T>0$, the lower threshold applies before the last phase, giving $1/n\le(1-1/n)^{T-1}C$ and the stated $+1$. No partial phase or idle phase after optimality is counted.
--
--   Differences from the source:
--   - encoding: circulations and cycles on a finite symmetric graph → published CircNetwork, IsCirculation, IsMinCost and residual simple-cycle conventions; reason: the same symmetric directed arcs, arbitrary real capacities and real flows are retained; m counts both orientations
--   - generalization: C is the maximum absolute integer arc cost → C is any natural upper bound on all absolute arc costs; reason: the source maximum is a natural number and is an allowed choice; larger bounds preserve the claimed inequality
--   - generalization: number of iterations in a completed execution → the bound holds for every finite execution prefix; reason: the same proof uses a nonoptimal state immediately before each next step, so it bounds prefixes without assuming termination
--   - reading: O(n log(nC)) outer phases, with the proof referring to the argument for Theorem 3.7 → T ≤ n ln(nC)+1 for C>0 and T=0 for C=0; reason: pp. 880–881 supply the exact shrink factor and integer threshold, yielding this explicit bound
--   - generalization: each iteration of Step 1 inside a cancel-and-tighten execution (starting at the current, ε(f,p)-optimal pair reached by the algorithm) → every admissible-cancellation prefix at any fixed prices from any circulation; reason: the p. 881 proof (each cancellation removes an admissible arc and creates only arcs of positive reduced cost) uses no property of the reached state, and Step 1 iterations are instances of this domain
-- source:
--   Goldberg, Tarjan, Finding Minimum-Cost Circulations by Canceling Negative Cycles, J. ACM 36(4), 1989, https://doi.org/10.1145/76359.76368, p. 880, Theorem 4.1; proof p. 881

import Mathlib
import Definitions.Def_CycleCanceling_MinMean_Supplement_CancelTighten

namespace CycleCanceling.MinMean.Supplement

/-- Theorem 4.1, pp. 880–881, in both cost regimes: the first clause has no
integrality restriction or initial-price restriction; only the second does. -/
theorem cancelTighten_bounds
    {V : Type*} [Fintype V] [DecidableEq V] (N : CircNetwork V)
    (hn : 2 ≤ Fintype.card V) (hm : Fintype.card V ≤ N.E.card) :
    (∀ (p : V → ℝ) (H : ℕ → V → V → ℝ) (K : ℕ),
      IsAdmissibleRun N p H K → K ≤ N.E.card) ∧
    ((∀ v w, (v, w) ∈ N.E → ∃ z : ℤ, N.c v w = (z : ℝ)) →
      ∀ (C : ℕ), (∀ v w, (v, w) ∈ N.E → |N.c v w| ≤ (C : ℝ)) →
      ∀ (F : ℕ → V → V → ℝ) (P : ℕ → V → ℝ) (T : ℕ),
        IsCancelTightenRun N F P T →
        if C = 0 then T = 0 else
          (T : ℝ) ≤ (Fintype.card V : ℝ) *
            Real.log ((Fintype.card V : ℝ) * (C : ℝ)) + 1) := by sorry

end CycleCanceling.MinMean.Supplement
