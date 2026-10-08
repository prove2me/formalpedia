-- Prove2me | Theorems.Thm_BurerMonteiro_RankIncrease_prop_2_1_optimal_iff
-- name    : BurerMonteiro.RankIncrease.prop_2_1_optimal_iff
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-04T11:38:58.686403+00:00
-- url     : https://prove2.me/theorems/14a842cb-576c-4227-bbb8-25fec54bd030
-- title:
--   Proposition 2.1: feasible $X$ and $(S,y)$ are simultaneously optimal iff $X\bullet S=0$
-- statement:
--   Consider the primal SDP (1) and the dual SDP (3) with symmetric data $C, A_1,\dots,A_m\in\mathcal S^n$ and $b\in\mathbb R^m$, under the standing assumptions of §2.1: $A_1,\dots,A_m$ are linearly independent, and some primal feasible $X^*$ and dual feasible $(S^*,y^*)$ satisfy $C\bullet X^*=b^Ty^*$. Let $X$ be primal feasible and $(S,y)$ dual feasible. Then
--   $$X\text{ is optimal for (1) and }(S,y)\text{ is optimal for (3)}\iff X\bullet S=0.$$
--
--   This is the complementary-slackness characterization of SDP optimality that the paper uses to turn the first-order condition $SR=0$ of the factorized problem into optimality for the SDP (Propositions 2.4 and 2.5).
--
--   **Formalization Note** Only the first clause of the proposition is formalized; the equivalent form $XS=SX=0$ is a separate matrix fact and is not part of this item. Optimality is over all feasible points of (1), respectively (3). The "only if" direction uses the zero-duality-gap assumption.
-- source:
--   Burer & Monteiro, A nonlinear programming algorithm for solving semidefinite programs via low-rank factorization (manuscript of March 9, 2001; Math. Program. 95 (2003)), p. 5, Proposition 2.1 (first clause), under the standing assumptions of §2.1, p. 4

import Mathlib
import Definitions.Def_BurerMonteiro_RankIncrease_SDP
import Definitions.Def_BurerMonteiro_RankIncrease_Nr

open Matrix
open scoped Matrix.Norms.Frobenius

namespace BurerMonteiro.RankIncrease

/-- Proposition 2.1, first clause (p. 5): under the standing assumptions, feasible solutions `X`
of (1) and `(S, y)` of (3) are simultaneously optimal if and only if `X • S = 0`. -/
theorem prop_2_1_optimal_iff {n m : ℕ} (C : Matrix (Fin n) (Fin n) ℝ)
    (A : Fin m → Matrix (Fin n) (Fin n) ℝ) (b : Fin m → ℝ) (hC : C.IsSymm)
    (hA : ∀ i, (A i).IsSymm) (hsa : StandingAssumptions C A b)
    (X S : Matrix (Fin n) (Fin n) ℝ) (y : Fin m → ℝ) (hX : IsPrimalFeasible A b X)
    (hSy : IsDualFeasible C A S y) :
    (IsPrimalOptimal C A b X ∧ IsDualOptimal C A b S y) ↔ frob X S = 0 := by sorry

end BurerMonteiro.RankIncrease
