-- Prove2me | solution 1 for hlawka_gap.lo_bound
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:27:39.199478+00:00
-- url     : https://prove2.me/submissions/0bfc5608-ba83-448a-802e-54f48de984e2

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Tactic



theorem solution {N1 N2 N3 M12 M23 M31 Mt : ℝ}
    (h12 : M12 ≤ N1 + N2) (h23 : M23 ≤ N2 + N3) (h31 : M31 ≤ N3 + N1)
    (hr1 : M23 - N1 ≤ Mt) (hr2 : M31 - N2 ≤ Mt) (hr3 : M12 - N3 ≤ Mt) :
    (N1 + N2 + N3 - Mt)
      ≤ ((N1 + N2 - M12) + (N2 + N3 - M23) + (N3 + N1 - M31))
        + 2 * min N1 (min N2 N3) := by
  have a : N1 + N2 + N3 - Mt ≤ ((N1 + N2 - M12) + (N2 + N3 - M23) + (N3 + N1 - M31)) + 2 * N1 := by linarith
  have b : N1 + N2 + N3 - Mt ≤ ((N1 + N2 - M12) + (N2 + N3 - M23) + (N3 + N1 - M31)) + 2 * N2 := by linarith
  have c : N1 + N2 + N3 - Mt ≤ ((N1 + N2 - M12) + (N2 + N3 - M23) + (N3 + N1 - M31)) + 2 * N3 := by linarith
  simp only [min_def]
  split_ifs <;> linarith

