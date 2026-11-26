-- Prove2me | Theorems.Thm_FixedMachinePrec_serialSchedule_meets_job_count
-- name    : FixedMachinePrec.serialSchedule_meets_job_count
-- status  : Proved
-- author  : @kj
-- created : 2026-11-26T12:23:56.561034+00:00
-- url     : https://prove2.me/theorems/609b836f-6345-5a5a-8ca9-50d64a5f6fa1
-- title:
--   The serial topological schedule meets the job-count deadline
-- statement:
--   For a finite acyclic precedence instance and at least one machine, the serial topological schedule realizes a feasible schedule that finishes by the number of jobs.
-- source:
--   Auxiliary statement for K. Jansen, Precedence Constraint Scheduling on a Fixed Number of Machines (1 November 2026), Lemma 5.2, p. 12 and Algorithm 6, p. 10.

import Mathlib
import Definitions.Def_FixedMachinePrec_Deadline

namespace FixedMachinePrec

theorem serialSchedule_meets_job_count (m : ℕ) (hm : 1 ≤ m) (G : Instance) (hG : G.Acyclic) : (serialSchedule G).MeetsDeadline m G.n := by sorry

end FixedMachinePrec
