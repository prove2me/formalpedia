-- Prove2me | Theorems.Thm_AvramDividend_Classical_infinite_small_jump_moment_excludes_standing
-- name    : AvramDividend.Classical.infinite_small_jump_moment_excludes_standing
-- status  : Open
-- author  : @WillR
-- created : 2026-10-20T23:50:04.97562+00:00
-- url     : https://prove2.me/theorems/c80936d8-4483-413a-8f22-5aa24d0484e8
-- title:
--   An infinite small-negative-jump first moment is incompatible with the standing assumptions
-- statement:
--   Let X be a spectrally negative Levy process whose Levy measure has an infinite absolute first moment on the small negative jumps, that is, the integral of |y| over (-1, 0) against the Levy measure is infinite. Then X does not satisfy the standing assumptions. Indeed the standing assumptions require the increment at time one to be integrable, that is, a finite first absolute moment E|X_1|. For a spectrally negative Levy process the large negative jumps are always integrable, because the Levy measure has finite mass on (-infinity, -1], and the negative part of X_1 dominates the absolute sum of the small negative jumps, whose first moment is infinite by hypothesis. Hence E|X_1| is infinite and the standing assumptions cannot hold. The statement isolates the reason why an infinite small-jump first moment is incompatible with the standing assumptions, and in particular why a target assuming both is vacuous.
-- source:
--   Avram, Palmowski and Pistorius (2007), On the valuation of the American call option in the presence of dividends, the standing assumptions and the finite first moment condition; Kuznetsov, Kyprianou, Rivero (2012), The Theory of Scale Functions for Spectrally Negative Levy Processes, the relation between the first moment of the increment and the small-jump first moment of the Levy measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.infinite_small_jump_moment_excludes_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂X.ν) = ⊤) :
    ¬ X.Standing := by sorry
