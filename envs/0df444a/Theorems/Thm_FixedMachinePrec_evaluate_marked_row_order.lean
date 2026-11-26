-- Prove2me | Theorems.Thm_FixedMachinePrec_evaluate_marked_row_order
-- name    : FixedMachinePrec.evaluate_marked_row_order
-- status  : Proved
-- author  : @kj
-- created : 2026-11-26T17:00:02.647831+00:00
-- url     : https://prove2.me/theorems/8d0de9e6-3760-4f05-956c-29e53b0dc8ab
-- title:
--   Smaller gap rows are available when a marked parent is visited
-- statement:
--   For a nonempty marked parent, all nonempty gap rows precede the parent by cardinality, and the empty row is initialized. If the parent update succeeds whenever the gap lookups succeed, acceptance of those gaps in the final table implies final acceptance of the parent. This isolates the evaluator’s row ordering from reachability in a single state graph.
-- source:
--   Auxiliary result for K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, 1 November 2026, Algorithm 4 and Theorem 5.9, pp. 9, 18.

import Mathlib
import Definitions.Def_FixedMachinePrec_EvaluateFamily
import Definitions.Def_FixedMachinePrec_Hierarchy

namespace FixedMachinePrec

theorem evaluate_marked_row_order {N : ℕ} (m : ℕ) (prec : Fin N → Fin N → Prop) [DecidableRel prec] (hm : 1 ≤ m) (hp : IsStrictOrder' prec) (F C : Finset (Finset (Fin N))) (h0 : ∅ ∈ F)
    (W : Finset (Fin N)) (hw : W ∈ F) (hne : W.Nonempty) (S : List (Finset (Fin N)))
    (hs : IsFullSchedule prec m W S) (marks : List ℕ) (hk : marks ≠ [])
    (hi : marks.Pairwise (· < ·)) (hr : ∀ t ∈ marks, 1 ≤ t ∧ t ≤ S.length)
    (hc : ∀ t ∈ marks, ∃ X ∈ C, slotsBetween S 0 t = W ∩ X)
(hg : ∀ A ∈ gaps S marks, (evaluateFamily prec m F C A).isSome = true)
    (hstep : ∀ tab : Table N, (∀ A ∈ gaps S marks, (lookup F tab A).isSome = true) →
      (processParent prec m F C tab W W).isSome = true) : (evaluateFamily prec m F C W).isSome = true := by sorry

end FixedMachinePrec
