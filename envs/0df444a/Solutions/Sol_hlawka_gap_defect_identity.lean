-- Prove2me | solution 1 for hlawka_gap.defect_identity
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:27:00.603039+00:00
-- url     : https://prove2.me/submissions/101325f4-ec3a-42b6-a3c9-8f07455defc4

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Tactic



theorem solution {N1 N2 N3 M12 M23 M31 Mt : ℝ} :
    (M12 + N3 - Mt)
      = (N3 + N1 - M31) + (N2 + N3 - M23)
        + ((N1 + N2 + N3 - Mt)
          - ((N1 + N2 - M12) + (N2 + N3 - M23) + (N3 + N1 - M31))) := by
  ring

