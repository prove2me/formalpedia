-- Prove2me | Theorems.Thm_FixedMachinePrec_replace_middle_block
-- name    : FixedMachinePrec.replace_middle_block
-- status  : Proved
-- author  : @kj
-- created : 2026-11-26T17:02:54.774021+00:00
-- url     : https://prove2.me/theorems/a058093f-0fa4-4aaf-b038-3fa782eca23f
-- title:
--   A full block may be replaced between fixed exterior schedules
-- statement:
--   A contiguous block of a full schedule can be replaced by any full schedule of precisely its union. The preceding and following lists remain fixed. This formulation applies to any parent domain and does not assume normalization.
-- source:
--   Auxiliary result for K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, 1 November 2026, Lemma 7.1, p. 32.

import Mathlib
import Definitions.Def_FixedMachinePrec_Separator

namespace FixedMachinePrec

theorem replace_middle_block {N : ℕ} (m : ℕ) (prec : Fin N → Fin N → Prop) [DecidableRel prec] (W U : Finset (Fin N)) (L A R B : List (Finset (Fin N)))
    (h : IsFullSchedule prec m W (L ++ A ++ R)) (hu : unionSlots A = U) (hb : IsFullSchedule prec m U B) :
    IsFullSchedule prec m W (L ++ B ++ R) := by sorry

end FixedMachinePrec
