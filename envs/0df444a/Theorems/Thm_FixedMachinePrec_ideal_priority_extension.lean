-- Prove2me | Theorems.Thm_FixedMachinePrec_ideal_priority_extension
-- name    : FixedMachinePrec.ideal_priority_extension
-- status  : Proved
-- author  : @kj
-- created : 2026-11-26T17:02:44.482668+00:00
-- url     : https://prove2.me/theorems/a7d5d178-c835-4c0e-bc6a-f4c34f52c0c0
-- title:
--   Put a specified ideal first in a linear extension
-- statement:
--   Every ideal of a finite induced precedence order is an initial segment of some priority list extending that order. The cutoff is exactly the cardinality of the ideal.
-- source:
--   Auxiliary result for K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, 1 November 2026, Corollary 7.5, second assertion, p. 37.

import Mathlib
import Definitions.Def_FixedMachinePrec_Separator

namespace FixedMachinePrec

theorem ideal_priority_extension {N : ℕ} (prec : Fin N → Fin N → Prop) (hp : IsStrictOrder' prec) (U I : Finset (Fin N))
    (hI : IsIdealIn prec U I) : ∃ pri : List (Fin N), IsPriorityList prec U pri ∧ priorityPrefix pri I.card = I := by sorry

end FixedMachinePrec
