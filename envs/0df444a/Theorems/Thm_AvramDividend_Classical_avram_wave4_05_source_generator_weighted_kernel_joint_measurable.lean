-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_generator_weighted_kernel_joint_measurable
-- name    : AvramDividend.Classical.avram_wave4_05_source_generator_weighted_kernel_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:49:42.04173+00:00
-- url     : https://prove2.me/theorems/917f8349-f674-4669-992b-55e717d0fe72
-- title:
--   Joint measurability of the true compensated source Lévy kernel
-- statement:
--   Under measurable scale W and measurable ordinary derivative W', the exact spectrally negative Levy generatorIntegrand W x y, with its indicator convention for the first-order small-jump compensator, is jointly measurable after multiplication by exp(-theta*x) and absolute value. This supplies an explicit joint-measurability input to the source compensated generator Fubini argument, not its integrability by itself.
-- source:
--   Exact SpectrallyNegativeLevy.generatorIntegrand and Mathlib measurable composition/indicator at pinned revision. Mission 1300fbe7-ca8c-49f9-a4de-4cb35ebd2f43.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Joint Borel measurability of the *actual* source compensated
    jump kernel and its exponentially weighted absolute value. -/

theorem AvramDividend.Classical.avram_wave4_05_source_generator_weighted_kernel_joint_measurable
    (W : ℝ → ℝ) (hW : Measurable W)
    (hdW : Measurable (deriv W)) (θ : ℝ) :
    Measurable
      (fun p : ℝ × ℝ => Real.exp (-θ * p.1) *
        |SpectrallyNegativeLevy.generatorIntegrand W p.1 p.2|) := by sorry
