-- Prove2me | solution 1 for hh_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T22:23:49.846427+00:00
-- url     : https://prove2.me/submissions/fea45814-1ae3-4675-b0e3-9a309a6c279e

import Definitions.Def_PrimeNumberTheoremAnd_Wiener

open Real

theorem solution (a : ℝ) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ hh a t := by
  unfold hh
  positivity
