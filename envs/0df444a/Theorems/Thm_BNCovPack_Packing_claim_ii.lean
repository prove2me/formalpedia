-- Prove2me | Theorems.Thm_BNCovPack_Packing_claim_ii
-- name    : BNCovPack.Packing.claim_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-05T18:18:46.999209+00:00
-- url     : https://prove2.me/theorems/69a47bfa-f292-42b5-aeb1-914681265147
-- title:
--   Theorem 3.1, proof, claim (ii) — the primal solution produced by the scheme is feasible
-- statement:
--   Consider the online fractional packing scheme of Section 3 with parameter $B>0$, run on an instance with $n\ge 1$ primal variables, costs $c(i)>0$, non-negative coefficients $a(i,j)$, and columns each of which has at least one positive entry. Let $x$ denote the primal solution held by the scheme. Then:
--
--   1. after every round $r\le m$, $x$ is feasible for the covering constraints revealed so far:
--   $$x(i)\ge 0\ \text{ for all } i,\qquad \sum_{i=1}^n a(i,k)\,x(i)\ge 1\ \text{ for every column } k\le r;$$
--   2. no primal variable ever decreases: the value of $x(i)$ after round $r+1$ is at least its value after round $r$.
--
--   Feasibility of the primal solution is half of the weak-duality argument that turns claim (i) into $B$-competitiveness. Part 2 is the paper's remark that "the values of the primal variables never decrease" (p. 5), which its proof of claim (ii) uses.
--
--   **Formalization Note** Columns are `Fin m`, 0-based, so "column $k\le r$" (1-based) is `(k : ℕ) < r`. The scheme is `stateAfter` of `BNCovPack.Packing.Scheme`.
-- source:
--   Buchbinder, Naor, Online Primal-Dual Algorithms for Covering and Packing, Math. Oper. Res. (2009), DOI 10.1287/moor.1080.0363, p. 5, Theorem 3.1, proof, claim (ii) (proved p. 6); monotonicity: p. 5, line 2

import Mathlib
import Definitions.Def_OnlinePrimalDual_GeneralPacking_GeneralInstance
import Definitions.Def_BNCovPack_Packing_Scheme

namespace BNCovPack.Packing

open OnlinePrimalDual.GeneralPacking

/-- Buchbinder–Naor 2009, proof of Theorem 3.1, claim (ii) (p. 5; proved p. 6): after every round
`r`, the primal solution `x` maintained by the scheme is feasible for the covering constraints
given so far (`x ≥ 0` and `∑ᵢ a(i,k) x(i) ≥ 1` for every column `k < r`), and no primal variable
ever decreases from one round to the next. -/
theorem claim_ii {I : Type*} [Fintype I] [Nonempty I] {m : ℕ}
    (inst : GeneralInstance I (Fin m)) (B : ℝ) (hB : 0 < B)
    (hcol : ∀ j : Fin m, ∃ i, 0 < inst.a i j) :
    (∀ r : ℕ, r ≤ m →
      (∀ i, 0 ≤ (stateAfter inst B r).x i) ∧
      (∀ k : Fin m, (k : ℕ) < r → 1 ≤ ∑ i, inst.a i k * (stateAfter inst B r).x i)) ∧
    (∀ r : ℕ, ∀ i, (stateAfter inst B r).x i ≤ (stateAfter inst B (r + 1)).x i) := by sorry

end BNCovPack.Packing
