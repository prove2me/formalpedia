-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_discounted_upperfirst_lintegral_le_measure_univ
-- name    : AvramDividend.Classical.chat04_discounted_upperfirst_lintegral_le_measure_univ
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:29:13.909291+00:00
-- url     : https://prove2.me/theorems/6ca1db46-ccb4-4bd6-aaf3-0893c0cf9ba8
-- title:
--   Any nonnegative-discount strict upper-first lower integral is bounded by total path-space mass
-- statement:
--   For every measure on the sample-path space and nonnegative discount, the strict upper-exit-before-ruin discounted reward lower integral is at most the total measure of the sample space. This holds for finite measures and changed laws without probability normalisation.
-- source:
--   Immediate consequence of the remotely accepted arbitrary-law discounted upper-first mass bound and monotonicity of measure.

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_discounted_upperfirst_mass_bound_any_measure

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_discounted_upperfirst_lintegral_le_measure_univ
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (q a x : ℝ) (hq : 0 ≤ q) :
    (∫⁻ ω,
      if twoSidedExitUpTime X (a - x) ω < twoSidedExitDownTime X (-x) ω then
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal (twoSidedExitUpTime X (a - x) ω))))
      else 0 ∂μ) ≤ μ Set.univ := by sorry
