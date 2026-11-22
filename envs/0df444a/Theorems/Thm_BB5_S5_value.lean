-- Prove2me | Theorems.Thm_BB5_S5_value
-- name    : BB5.S5_value
-- status  : Open
-- author  : @loader3229
-- created : 2026-11-21T16:08:14.32151+00:00
-- url     : https://prove2.me/theorems/fe797323-bf3a-4bd6-b1d4-5008e7aaf0fe
-- title:
--   Theorem 1.1: $S(5) = 47{,}176{,}870$
-- statement:
--   The fifth Busy Beaver value: the maximum number of steps a 5-state, 2-symbol Turing machine can perform from the all-zero tape before halting is exactly $47{,}176{,}870$.
-- source:
--   arXiv:2509.12337, https://arxiv.org/abs/2509.12337, Theorem 1.1 (Coq-BB5 Lemma BB5_value)

import Mathlib
import Definitions.Def_FCP_BusyBeaver

import Mathlib
import Definitions.Def_FCP_BusyBeaver

namespace BB5

/-- Theorem 1.1 of arXiv:2509.12337 (bbchallenge Collaboration et al.,
"Determination of the fifth Busy Beaver value"): S(5) = 47,176,870.
Here `FCP.BusyBeaver.BB` is the maximum-shifts busy beaver function, i.e. the
maximum number of transitions an `n`-state, 2-symbol Turing machine performs
from the all-zero tape before halting. -/
theorem S5_value : FCP.BusyBeaver.BB 5 = 47176870 := by
  sorry

end BB5
