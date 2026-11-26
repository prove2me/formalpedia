-- Prove2me | Theorems.Thm_FixedMachinePrec_normalized_prefix_separator
-- name    : FixedMachinePrec.normalized_prefix_separator
-- status  : Open
-- author  : @kj
-- created : 2026-11-26T17:03:05.246947+00:00
-- url     : https://prove2.me/theorems/1bf897f8-6973-4cab-9fb9-0c00c4c5f186
-- title:
--   A normalized priority cutoff admits a separating slot
-- statement:
--   For a nonempty normalized schedule, each cutoff in the priority order has an actual separating slot in that same schedule. This is the normalized-schedule assertion of the corollary.
-- source:
--   Auxiliary result for K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, 1 November 2026, Corollary 7.5, first assertion, p. 37.

import Mathlib
import Definitions.Def_FixedMachinePrec_Separator

namespace FixedMachinePrec

theorem normalized_prefix_separator {N : ℕ} (m : ℕ) (prec : Fin N → Fin N → Prop) [DecidableRel prec] (hm : 3 ≤ m) (hprec : IsStrictOrder' prec) (U : Finset (Fin N)) (hne : U.Nonempty)
    (pri : List (Fin N)) (hp : IsPriorityList prec U pri) (Zs : List (Finset (Fin N)))
    (hz : IsNormalized prec m U pri Zs) (k : ℕ) (hk : k ≤ U.card) :
    ∃ r : ℕ, Separates prec Zs (priorityPrefix pri k) r := by sorry

end FixedMachinePrec
