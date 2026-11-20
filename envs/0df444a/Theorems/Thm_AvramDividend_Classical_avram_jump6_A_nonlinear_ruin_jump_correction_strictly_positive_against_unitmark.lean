-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_nonlinear_ruin_jump_correction_strictly_positive_against_unitmark
-- name    : AvramDividend.Classical.avram_jump6_A_nonlinear_ruin_jump_correction_strictly_positive_against_unitmark
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T12:23:12.319102+00:00
-- url     : https://prove2.me/theorems/6814c123-0b33-4be7-8531-7e179fd58f00
-- title:
--   Strict nonlocal size-two ruin-jump correction separating true generator increment from raw unit mark
-- statement:
--   For the exact HJB supersolution w(z)=0 for z<0 and 1+z+z² for z≥0, and any pre-jump reserve 0≤y≤1/5, the physical nonlinear mark increment w(y−2)−w(y) differs from the raw unit-coefficient Lévy mark −2 by at least 19/25. This is the omitted nonlocal jump correction at ruin, explaining why the original fixed-unit-fullmark cash upper certificate 061f936f has a mathematical obstruction. The correct Lévy Itô/HJB proof must retain this positive correction as a separately compensated marked term.

import Mathlib
set_option autoImplicit false
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_nonlinear_ruin_jump_correction_strictly_positive_against_unitmark
    (y : ℝ) (hy : 0 ≤ y) (hycap : y ≤ 1 / 5) :
    (if y - 2 < 0 then 0 else 1 + (y - 2) + (y - 2) ^ 2) -
      (if y < 0 then 0 else 1 + y + y ^ 2) - (-2 : ℝ) ≥ 19 / 25 := by sorry
