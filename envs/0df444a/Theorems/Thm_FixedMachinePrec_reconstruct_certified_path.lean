-- Prove2me | Theorems.Thm_FixedMachinePrec_reconstruct_certified_path
-- name    : FixedMachinePrec.reconstruct_certified_path
-- status  : Proved
-- author  : @kj
-- created : 2026-11-26T12:23:53.757747+00:00
-- url     : https://prove2.me/theorems/11b636d5-882f-5f4b-9537-58a94a46c453
-- title:
--   Soundness of reconstruction along a certified marked path
-- statement:
--   Suppose every stored schedule is sound. From a nonempty certified edge path in the parent state graph whose initial prefix and final suffix have successful lookups, Algorithm 5 reconstructs a full schedule of the parent. This is a claim about concatenating feasible pieces across ideal boundaries, independent of how the path was found.
-- source:
--   Auxiliary statement for K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines (1 November 2026), Theorem 5.6, p. 14 and Algorithm 5, p. 9.

import Mathlib
import Definitions.Def_FixedMachinePrec_EvaluateFamily

namespace FixedMachinePrec

theorem reconstruct_certified_path {N : ℕ} (m : ℕ) (prec : Fin N → Fin N → Prop) [DecidableRel prec] (hm : 1 ≤ m) (F C : Finset (Finset (Fin N))) (W : Finset (Fin N)) (tab : Table N)
    (hs : ∀ X S, tab X = some S → IsFullSchedule prec m X S) (p : ℕ → PredField) (t : ℕ) :
    let st := buildStates prec m C W
    let lk := fun X => (lookup F tab X).isSome
    let path := tracePath p st.length t
    (∃ a, st[t]? = some a ∧ lk a.R = true) →
    (∃ i rest, path = i :: rest ∧ (∃ a, st[i]? = some a ∧ lk a.L = true) ∧
      path.getLast? = some t ∧ path.IsChain (fun i j => edge st lk i j = true)) →
    IsFullSchedule prec m W (reconstruct st (fun X => (lookup F tab X).getD []) p t) := by sorry

end FixedMachinePrec
