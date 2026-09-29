-- Prove2me | solution 1 for mme_CW_support_pattern_symmetric
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-05-31T18:06:26.49355+00:00
-- url     : https://prove2.me/submissions/0e367a30-e9b7-4713-8ab8-d83602cdd455

import Definitions.Def_mme_CW_support_pattern
import Definitions.Def_mme_laser_pattern

open MME

theorem solution : LaserSymmetric CWSupportPattern := by
  intro x hx
  fin_cases hx <;> decide
