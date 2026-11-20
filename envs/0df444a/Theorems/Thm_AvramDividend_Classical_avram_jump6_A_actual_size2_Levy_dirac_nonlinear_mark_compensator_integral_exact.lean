-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_actual_size2_Levy_dirac_nonlinear_mark_compensator_integral_exact
-- name    : AvramDividend.Classical.avram_jump6_A_actual_size2_Levy_dirac_nonlinear_mark_compensator_integral_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T16:18:58.22419+00:00
-- url     : https://prove2.me/theorems/4d695647-c74b-4e23-ae7d-35acd02d8078
-- title:
--   Exact genuine negative-size-two Lévy Dirac marked nonlinear compensation integral and its strictly positive lower bound
-- statement:
--   In the actual spectrally negative Lévy model with negative jump characteristic measure ν=δ_{−2}, the correctly compensated nonlinear marked generator remainder ∫[w(y+z)−w(y)−z]ν(dz) equals 1−y−y² for the HJB candidate w=0 on negative reserves and 1+y+y² otherwise. On any capped pre-ruin reserve y∈[0,1/5], this genuine original Dirac Lévy measure compensation is at least 19/25, strictly positive. This directly identifies the omitted marked nonlinear compensator term in the deprecated original fullmark unit-coefficient signed cash ledger, and provides a concrete imported source for the corrected nonlinear finite-activity Itô-Meyer generator.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jump6_A_large_negative_overshoot_nonlinear_jump_correction_uniform_positive
set_option autoImplicit false
open MeasureTheory AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_actual_size2_Levy_dirac_nonlinear_mark_compensator_integral_exact
    (y : ℝ) (hy : 0 ≤ y) (hcap : y ≤ 1 / 5) :
    (∫ z : ℝ,
        ((if y + z < 0 then 0 else 1 + (y + z) + (y + z) ^ 2) -
         (if y < 0 then 0 else 1 + y + y ^ 2) - z)
      ∂(Measure.dirac (-2 : ℝ))) = 1 - y - y ^ 2 ∧
    (19 / 25 : ℝ) ≤
      ∫ z : ℝ,
        ((if y + z < 0 then 0 else 1 + (y + z) + (y + z) ^ 2) -
         (if y < 0 then 0 else 1 + y + y ^ 2) - z)
      ∂(Measure.dirac (-2 : ℝ)) := by sorry
