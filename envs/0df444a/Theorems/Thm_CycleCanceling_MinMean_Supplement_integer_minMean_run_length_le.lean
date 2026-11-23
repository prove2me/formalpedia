-- Prove2me | Theorems.Thm_CycleCanceling_MinMean_Supplement_integer_minMean_run_length_le
-- name    : CycleCanceling.MinMean.Supplement.integer_minMean_run_length_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-11-23T10:21:33.171343+00:00
-- url     : https://prove2.me/theorems/168e83b9-3733-4055-a330-cd84e33f88b6
-- title:
--   Theorem 3.7 — integer-cost minimum-mean cancellation bound
-- statement:
--   Let $N$ have $m=|E|\ge n=|V|\ge2$, real capacities and integer arc costs. Let $C$ be any natural upper bound on their absolute values. Start at any circulation and take any $K$-step prefix of the published minimum-mean cycle-canceling algorithm, with arbitrary tie choices. Then
--
--   $$\begin{cases}K=0,&C=0,\\ K\le m\bigl(n\ln(nC)+1\bigr),&C>0.\end{cases}$$
--
--   The paper prints $O(nm\log(nC))$; its proof gives the displayed explicit bound. This supplies the integer-cost companion to the real-cost goal, without restricting capacities or initial flows to integers.
--
--   **Formalization Note** The logarithm is natural. For a positive prefix, the proof uses $j=\lfloor(K-1)/m\rfloor\le n\ln(nC)$ and $K\le m(j+1)$. The zero-cost case is separate, so no logarithm at zero contributes to the bound. The proof's citation to Theorem 3.1 for the integer threshold refers to Theorem 3.2.
--
--   Differences from the source:
--   - encoding: circulations and cycles on a finite symmetric graph → published CircNetwork, IsCirculation, IsMinCost and residual simple-cycle conventions; reason: the same symmetric directed arcs, arbitrary real capacities and real flows are retained; m counts both orientations
--   - generalization: C is the maximum absolute integer arc cost → C is any natural upper bound on all absolute arc costs; reason: the source maximum is a natural number and is an allowed choice; larger bounds preserve the claimed inequality
--   - generalization: number of iterations in a completed execution → the bound holds for every finite execution prefix; reason: the same proof uses a nonoptimal state immediately before each next step, so it bounds prefixes without assuming termination
--   - reading: O(nm log(nC)) in the statement, with j ≤ n ln(nC) in the proof → K ≤ m(n ln(nC)+1) for C>0 and K=0 for C=0; reason: the p. 879 proof pins the constant and supplies the missing zero-cost boundary
-- source:
--   Goldberg, Tarjan, Finding Minimum-Cost Circulations by Canceling Negative Cycles, J. ACM 36(4), 1989, https://doi.org/10.1145/76359.76368, p. 879, Theorem 3.7

import Mathlib
import Definitions.Def_CycleCanceling_MinMean_Algorithm

namespace CycleCanceling.MinMean.Supplement

/-- Theorem 3.7, p. 879, with its proof's explicit bound; C=0 terminates immediately. -/
theorem integer_minMean_run_length_le
    {V : Type*} [Fintype V] [DecidableEq V] (N : CircNetwork V)
    (hn : 2 ≤ Fintype.card V) (hm : Fintype.card V ≤ N.E.card)
    (hInt : ∀ v w, (v, w) ∈ N.E → ∃ z : ℤ, N.c v w = (z : ℝ))
    (C : ℕ) (hC : ∀ v w, (v, w) ∈ N.E → |N.c v w| ≤ (C : ℝ))
    (F : ℕ → V → V → ℝ) (K : ℕ) (hRun : IsMinMeanRun N F K) :
    if C = 0 then K = 0 else
      (K : ℝ) ≤ (N.E.card : ℝ) *
        ((Fintype.card V : ℝ) * Real.log ((Fintype.card V : ℝ) * (C : ℝ)) + 1) := by sorry

end CycleCanceling.MinMean.Supplement
