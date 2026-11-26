-- Prove2me | Theorems.Thm_FixedMachinePrec_accepted_gaps_accept_parent
-- name    : FixedMachinePrec.accepted_gaps_accept_parent
-- status  : Open
-- author  : @kj
-- created : 2026-11-26T12:24:00.29806+00:00
-- url     : https://prove2.me/theorems/37da83f7-72e5-4e95-a64d-65f83a4bb6ae
-- title:
--   Acceptance propagates from the gaps to a marked parent
-- statement:
--   Consider a single nonempty representable parent with a feasible marked schedule and representable cuts. If all open gaps of that schedule are accepted by the evaluator, then it accepts the parent. The gap rows are smaller and therefore available before the parent; the marks give a path of state records. No hierarchy assumption on the gaps is needed.
-- source:
--   Auxiliary statement for K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines (1 November 2026), Theorem 5.9, p. 18 and Definition 5.7, p. 15.

import Mathlib
import Definitions.Def_FixedMachinePrec_EvaluateFamily
import Definitions.Def_FixedMachinePrec_Hierarchy

namespace FixedMachinePrec

theorem accepted_gaps_accept_parent {N : ℕ} (m : ℕ) (prec : Fin N → Fin N → Prop) [DecidableRel prec] (hm : 1 ≤ m) (hp : IsStrictOrder' prec) (F C : Finset (Finset (Fin N))) (h0 : ∅ ∈ F)
    (W : Finset (Fin N)) (hw : W ∈ F) (hne : W.Nonempty) (S : List (Finset (Fin N)))
    (hs : IsFullSchedule prec m W S) (marks : List ℕ) (hk : marks ≠ [])
    (hi : marks.Pairwise (· < ·)) (hr : ∀ t ∈ marks, 1 ≤ t ∧ t ≤ S.length)
    (hc : ∀ t ∈ marks, ∃ X ∈ C, slotsBetween S 0 t = W ∩ X)
    (hg : ∀ A ∈ gaps S marks, (evaluateFamily prec m F C A).isSome = true) :
    (evaluateFamily prec m F C W).isSome = true := by sorry

end FixedMachinePrec
