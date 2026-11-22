-- Prove2me | Theorems.Thm_BB5_upper_bound
-- name    : BB5.upper_bound
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-21T16:07:12.506461+00:00
-- url     : https://prove2.me/theorems/133f0aa1-6e63-48e2-a62c-59559ff66b4e
-- title:
--   Upper bound: $S(5) \le 47{,}176{,}870$
-- statement:
--   Upper bound on the fifth Busy Beaver value: $S(5)\le 47{,}176{,}870$. This is the main difficulty: all 5-state machines are enumerated in Tree Normal Form (181,385,789 machines) and their halting behaviour decided, with 13 sporadic machines handled by individual non-halting proofs.
-- source:
--   arXiv:2509.12337, https://arxiv.org/abs/2509.12337, Lemma BB5_upperbound

import Mathlib
import Definitions.Def_FCP_BusyBeaver

import Mathlib
import Definitions.Def_FCP_BusyBeaver

namespace BB5

/-- Upper bound for the fifth Busy Beaver value (Lemma BB5_upperbound):
S(5) ≤ 47,176,870. This is the main difficulty of the paper: every 5-state
machine is enumerated in Tree Normal Form (181,385,789 machines) and its
halting behaviour decided by the decider pipeline, with 13 sporadic machines
handled by individual non-halting proofs. -/
theorem upper_bound : FCP.BusyBeaver.BB 5 ≤ 47176870 := by
  sorry

end BB5
