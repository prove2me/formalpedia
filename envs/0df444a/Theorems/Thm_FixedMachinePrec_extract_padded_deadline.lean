-- Prove2me | Theorems.Thm_FixedMachinePrec_extract_padded_deadline
-- name    : FixedMachinePrec.extract_padded_deadline
-- status  : Proved
-- author  : @kj
-- created : 2026-11-26T12:24:05.832921+00:00
-- url     : https://prove2.me/theorems/a7de2765-0268-4395-a030-f82d031fc09c
-- title:
--   Deleting dummy jobs yields a feasible schedule
-- statement:
--   Suppose all original job labels fit in the padded instance. From any full padded schedule with $T$ slots, deleting the dummies and assigning machines by increasing original job label yields a feasible schedule meeting deadline $T$.
-- source:
--   Auxiliary statement for K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines (1 November 2026), Lemma 5.2, p. 12 and Algorithm 6, p. 10.

import Mathlib
import Definitions.Def_FixedMachinePrec_Deadline

namespace FixedMachinePrec

theorem extract_padded_deadline (G : Instance) (m T : ℕ) (hsize : G.n ≤ m*T) (S : List (Finset (Fin (m*T)))) (h : IsFullSchedule (paddedPrec G (m*T)) m Finset.univ S) (hlen : S.length = T) : (extractSchedule G S).MeetsDeadline m T := by sorry

end FixedMachinePrec
