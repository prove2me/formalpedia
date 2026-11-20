-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_Levy_generator_nonlinear_large_negative2_mark_exact
-- name    : AvramDividend.Classical.avram_jump6_A_original_Levy_generator_nonlinear_large_negative2_mark_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:39:14.09535+00:00
-- url     : https://prove2.me/theorems/17cbcdef-c3b0-4348-beb5-785cb0e4e0b0
-- title:
--   Exact original Lévy generator nonlinear large negative mark kernel at a genuine size-two ruin jump
-- statement:
--   In the exact original spectrally negative Lévy generator definition, the negative size-two Poisson mark z=−2 is outside the small-jump truncation interval (−1,1). For the original discounted-dividend candidate w(z)=0 for z<0 and w(z)=1+z+z² for z≥0, and genuine capped pre-ruin reserve y∈[0,1/5], the true nonlinear generator mark kernel equals w(y−2)−w(y)=−(1+y+y²), strictly negative. This identifies the correct original large-negative-jump compensator term to restore to the deprecated raw fullmark Ito cash source. The companion correction against unit-coefficient Jfull is positive; both pieces must be kept separate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_Levy_generator_nonlinear_large_negative2_mark_exact
    (y : ℝ) (hy : 0 ≤ y) (hcap : y ≤ 1 / 5) :
    SpectrallyNegativeLevy.generatorIntegrand
      (fun z : ℝ => if z < 0 then 0 else 1 + z + z ^ 2)
      y (-2 : ℝ) = -(1 + y + y ^ 2) := by sorry
