-- Prove2me | solution 1 for hlawka_gap.telescoping
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-18T20:27:20.43452+00:00
-- url     : https://prove2.me/submissions/5ca7852b-79fd-4373-aa69-a5e0ae9192cc

import Mathlib
import Mathlib.Data.Real.Basic
import Mathlib.Tactic



theorem solution {N1 N2 N3 M12 Mt : ℝ} :
    (N1 + N2 + N3 - Mt) = (N1 + N2 - M12) + (M12 + N3 - Mt) := by
  ring

