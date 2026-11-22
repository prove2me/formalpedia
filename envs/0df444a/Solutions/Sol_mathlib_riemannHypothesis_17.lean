-- Prove2me | solution 17 for mathlib_riemannHypothesis
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T21:26:07.911355+00:00
-- url     : https://prove2.me/submissions/435a0297-6c80-4173-915b-73c8352b6b1d
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Mathlib
import Theorems.Thm_MasulloRH_regular_width_one_sided_trace
import Theorems.Thm_MasulloAudit_one_sided_regular_windows_iff_RH

theorem solution : RiemannHypothesis :=
  MasulloAudit.one_sided_regular_windows_iff_RH.mp
    (fun β hβ hreg φ hφ hpos =>
      MasulloRH.regular_width_one_sided_trace β hβ hreg φ hφ hpos)
