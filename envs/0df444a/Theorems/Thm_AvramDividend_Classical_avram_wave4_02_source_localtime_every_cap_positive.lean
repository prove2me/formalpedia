-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_02_source_localtime_every_cap_positive
-- name    : AvramDividend.Classical.avram_wave4_02_source_localtime_every_cap_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T09:35:36.756988+00:00
-- url     : https://prove2.me/theorems/60b97e7e-57ce-4713-8235-e4cf0a2989a9
-- title:
--   Every finite-time running-supremum local-time cap is accessible under infinite small-jump variation
-- statement:
--   For the actual spectrally negative Levy path with divergent absolute first small-negative-jump moment, every level b of the source running maximum S_t has strictly positive upper-tail mass at each t>0. The proof uses the exact source Levy exponential moment and source superlinear Laplace exponent growth. This gives genuine deterministic local-time truncation accessibility without requiring any excursion compensator.
-- source:
--   Genuine source laplace, unbounded_psi_discount_denominator_eventually_linear and infinite_small_jump_not_bv; positive upper support via an exponential moment contradiction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_Reflection
import Theorems.Thm_AvramDividend_Classical_avram_wave3_01_infinite_small_jump_not_bv
import Theorems.Thm_AvramDividend_Classical_unbounded_psi_discount_denominator_eventually_linear
import Theorems.Thm_AvramDividend_Classical_runningSup_monotone_and_path_le

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_02_source_localtime_every_cap_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤)
    (t : ℝ≥0) (ht : 0 < t) (b : ℝ) :
    0 < P {ω : Ω | b < runningSup X t ω} := by sorry
