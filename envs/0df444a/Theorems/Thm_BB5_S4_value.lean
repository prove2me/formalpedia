-- Prove2me | Theorems.Thm_BB5_S4_value
-- name    : BB5.S4_value
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-21T16:07:39.725092+00:00
-- url     : https://prove2.me/theorems/fa5ef3d8-9bcc-4da2-8eb2-a307e055b0c3
-- title:
--   Theorem 6.3: $S(4) = 107$
-- statement:
--   Confirmation of Brady's 1983 result: $S(4)=107$, re-established by the S(4) decider pipeline of Coq-BB5.
-- source:
--   arXiv:2509.12337, https://arxiv.org/abs/2509.12337, Theorem 6.3

import Mathlib
import Definitions.Def_FCP_BusyBeaver

import Mathlib
import Definitions.Def_FCP_BusyBeaver

namespace BB5

/-- Theorem 6.3 of arXiv:2509.12337 (confirmation of Brady's 1983 result):
S(4) = 107. This is a smaller Busy Beaver value that Coq-BB5 re-establishes
with its S(4) decider pipeline. -/
theorem S4_value : FCP.BusyBeaver.BB 4 = 107 := by
  sorry

end BB5
