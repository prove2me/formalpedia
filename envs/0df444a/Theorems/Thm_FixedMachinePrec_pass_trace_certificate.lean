-- Prove2me | Theorems.Thm_FixedMachinePrec_pass_trace_certificate
-- name    : FixedMachinePrec.pass_trace_certificate
-- status  : Proved
-- author  : @kj
-- created : 2026-11-26T12:23:49.192461+00:00
-- url     : https://prove2.me/theorems/2eeda5ef-8ca8-50f3-9d73-313e36578b83
-- title:
--   Marked records have bounded predecessor certificates
-- statement:
--   For any record list, following the final predecessor of a marked record yields an edge path from an initial record with START predecessor to that record, using at most as many records as the input list. This certificate property needs no assumption that the bucket order is topological: a new predecessor always points to an already marked record.
-- source:
--   Auxiliary statement for K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines (1 November 2026), Lemma 5.5, p. 14 and Algorithm 4, p. 9.

import Mathlib
import Definitions.Def_FixedMachinePrec_EvaluateFamily

namespace FixedMachinePrec

theorem pass_trace_certificate {N : ℕ} (st : List (StateRec N)) (lk : Finset (Fin N) → Bool) (j : ℕ) (hj : j < st.length) (hm : (reachPass st lk).1 j = true) : let p := (reachPass st lk).2; let path := tracePath p st.length j; ∃ i rest, path = i :: rest ∧ (∃ a, st[i]? = some a ∧ lk a.L = true) ∧ p i = .start ∧ path.getLast? = some j ∧ path.IsChain (fun x y => edge st lk x y = true) := by sorry

end FixedMachinePrec
