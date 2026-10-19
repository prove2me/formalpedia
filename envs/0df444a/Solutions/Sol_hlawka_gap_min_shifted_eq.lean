-- Prove2me | solution 1 for hlawka_gap.min_shifted_eq
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:27:56.404445+00:00
-- url     : https://prove2.me/submissions/21b32e45-d567-49f6-b59d-d34123ca2f84

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Tactic



theorem solution {N1 N2 N3 M12 M23 M31 Mt : ℝ} :
    min (min (M12 + N3 - Mt) (M23 + N1 - Mt)) (M31 + N2 - Mt)
      = (N1 + N2 + N3 - Mt)
        - max (N1 + N2 - M12) (max (N2 + N3 - M23) (N3 + N1 - M31)) := by
  simp only [min_def, max_def]
  split_ifs <;> linarith

