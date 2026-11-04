-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_original_epsilon_drift_identification
-- name    : AvramDividend.Classical.avram_p4_c_generator_original_epsilon_drift_identification
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:42:59.071253+00:00
-- url     : https://prove2.me/theorems/762f5d2b-6ff5-4e29-a913-87ccc25950fc
-- title:
--   Full original Lévy generator equals epsilon-compensated physical drift plus separated untruncated jumps and small-jump remainder
-- statement:
--   For the genuine source Lévy generator, original GeneratorIntegrable w y, and any strict 0<epsilon<1, identify the full source diffusion-plus-drift-plus-compensator expression with epsilon-renormalised drift c −∫_{(-1,-epsilon)}z ν(dz), full uncorrected jump increments on z≤-1 and -1<z<-epsilon, and exact compensated small-jump remainder on -epsilon≤z<0. This explicitly includes possible jump-mass at z=-1 and excludes -epsilon from the large band. No global absolute first jump moment is assumed. The theorem is an algebraic source-identity and does not assert stochastic compensation or stopped Ito–Meyer.
-- source:
--   Original SpectrallyNegativeLevy.generator/GeneratorIntegrable, Proved epsilon split 5434bf03, finite drift renormalisation dde11d7a, and source exact z≤-1 jump identity 5bce7b49. Avram–Palmowski–Pistorius Eq (5.13).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_original_epsilon_drift_identification
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (y ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hgen : X.GeneratorIntegrable w y) :
    X.generator w y =
      X.σ ^ 2 / 2 * iteratedDeriv 2 w y +
      (X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) * deriv w y +
      (∫ z in Iic (-1 : ℝ), w (y + z) - w y ∂X.ν) +
      (∫ z in Ioo (-1 : ℝ) (-ε), w (y + z) - w y ∂X.ν) +
      (∫ z in Ico (-ε) 0,
        SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) := by sorry
