-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_original_epsilon_drift_compact
-- name    : AvramDividend.Classical.avram_p4_c_generator_original_epsilon_drift_compact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:56:33.081332+00:00
-- url     : https://prove2.me/theorems/4ca1c36a-241c-4736-9e84-86ee268448ad
-- title:
--   Original Lévy generator with one uncompensated large-jump integral and epsilon-physical drift
-- statement:
--   For 0<epsilon<1 under exactly source GeneratorIntegrable, identify the original source generator with the physical epsilon-renormalised drift c - integral_{-1<z<-epsilon} z nu, its Gaussian second-order term, the full uncorrected jump integral over all z<-epsilon, and the compensated small-jump remainder over -epsilon≤z<0. Endpoint -1 is retained as an uncompensated jump. Algebraic identification only; no stochastic compensation assumed.
-- source:
--   P4-C original_epsilon_drift_identification and raw_large_cutoff_unit_partition

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_c_generator_original_epsilon_drift_compact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (w : ℝ → ℝ) (y ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hgen : X.GeneratorIntegrable w y) :
    X.generator w y =
      X.σ ^ 2 / 2 * iteratedDeriv 2 w y +
      (X.c - (∫ z in Ioo (-1 : ℝ) (-ε), z ∂X.ν)) * deriv w y +
      (∫ z in Iio (-ε), w (y + z) - w y ∂X.ν) +
      (∫ z in Ico (-ε) 0,
        SpectrallyNegativeLevy.generatorIntegrand w y z ∂X.ν) := by sorry
