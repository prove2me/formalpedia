-- Prove2me | Theorems.Thm_FixedMachinePrec_priority_exchange_decreases_encoding
-- name    : FixedMachinePrec.priority_exchange_decreases_encoding
-- status  : Proved
-- author  : @kj
-- created : 2026-11-26T17:02:42.89675+00:00
-- url     : https://prove2.me/theorems/49e4d3df-82cc-44d5-8277-684180bc8e88
-- title:
--   A higher-priority exchange improves the first differing slot
-- statement:
--   Suppose two full schedules of the same jobs agree through slot $r$. Swapping a job in slot $r$ of the second with a later job of strictly higher priority yields an encoding lexicographically smaller than that of the first schedule, irrespective of the suffix or whether the exchange is feasible.
-- source:
--   Auxiliary result for K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines, 1 November 2026, Lemma 7.1, pp. 30–32.

import Mathlib
import Definitions.Def_FixedMachinePrec_Separator

namespace FixedMachinePrec

theorem priority_exchange_decreases_encoding {N : ℕ} (m : ℕ) (prec : Fin N → Fin N → Prop) [DecidableRel prec] (U : Finset (Fin N)) (pri : List (Fin N)) (hp : IsPriorityList prec U pri)
    (Zs ρ : List (Finset (Fin N))) (hZ : IsFullSchedule prec m U Zs) (hρ : IsFullSchedule prec m U ρ)
    (r : ℕ) (hr : 1 ≤ r) (hb : r ≤ Zs.length) (he : ρ.take r = Zs.take r)
    (x y : Fin N) (hy : y ∈ ρ.getD (r-1) ∅) (hx : x ∈ U) (hl : r < localTime ρ x)
    (hprio : pri.idxOf x < pri.idxOf y) : priEnc pri (swapJobs ρ x y) < priEnc pri Zs := by sorry

end FixedMachinePrec
