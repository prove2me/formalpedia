-- Prove2me | Theorems.Thm_BudgetClock_Subadditive_value_monotone
-- name    : BudgetClock.Subadditive.value_monotone
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-14T06:25:16.575983+00:00
-- url     : https://prove2.me/theorems/f3c534c3-dba2-4c9d-bb3d-fcef40456b39
-- title:
--   §5, p. 15 — the value of Mechanism 4's output is non-decreasing in the number of phases
-- statement:
--   Let $v : 2^N \to \mathbb{R}$ be any set function on the $n$ bidders, $c$ any cost vector, $B$ any budget and $\mathrm{alg}$ any subroutine. Write $S_{\mathrm{final}}(F)$ for the set returned by Mechanism 4 when the main loop is allowed at most $F$ phases. Then for all $F \le F'$,
--
--   $$v\big(S_{\mathrm{final}}(F)\big) \le v\big(S_{\mathrm{final}}(F')\big).$$
--
--   This is the paper's observation that keeping two solutions $S_{\mathrm{prev}}$ and $S_{\mathrm{curr}}$ makes the value obtained by the auction monotone non-decreasing: a phase replaces $S_{\mathrm{prev}}$ by the better of the two current solutions, so the value of the eventual output never drops. It is the step that lets the analysis of Theorem 8 charge the output with the value of any set found in an earlier phase.
--
--   **Formalization Note** The statement needs none of the standing hypotheses (non-negativity, subadditivity, costs, budget, oracle guarantee), so it is stated without them; it is stronger than the paper's remark.
-- source:
--   Balkanski et al., Deterministic Budget-Feasible Clock Auctions, arXiv:2107.09239v2, p. 15, §5, paragraph after Mechanism 4

import Mathlib
import Definitions.Def_BudgetClock_Subadditive_Mechanism

namespace BudgetClock.Subadditive

theorem value_monotone {n : ℕ} (v : Finset (Fin n) → ℝ) (c : Fin n → ℝ) (B : ℝ)
    (alg : ℕ → Finset (Fin n) → Finset (Fin n)) (F F' : ℕ) (hFF' : F ≤ F') :
    v (mechanism4 v c B alg F).1 ≤ v (mechanism4 v c B alg F').1 := by sorry

end BudgetClock.Subadditive
