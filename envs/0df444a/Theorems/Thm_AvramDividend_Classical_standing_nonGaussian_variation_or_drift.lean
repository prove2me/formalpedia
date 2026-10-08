-- Prove2me | Theorems.Thm_AvramDividend_Classical_standing_nonGaussian_variation_or_drift
-- name    : AvramDividend.Classical.standing_nonGaussian_variation_or_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T16:46:34.984183+00:00
-- url     : https://prove2.me/theorems/7a596821-fcf0-406e-90ad-e376ce232534
-- title:
--   Non-Gaussian standing process has infinite first moment or positive drift
-- statement:
--   For a canonical spectrally negative Lévy process satisfying Avram's Standing assumptions with zero Gaussian coefficient, either the small-negative-jump absolute first moment is infinite or the process has strictly positive compensated drift. This formal dichotomy is the first case split needed to prove eventual positivity of the exponent beyond the Gaussian branch.
-- source:
--   Unfold SpectrallyNegativeLevy.Standing, BoundedVariation, and HasMonotonePaths. If the first moment is finite and sigma=0 then the process has bounded variation; Standing rules out drift ≤0, so drift>0. Otherwise the ENNReal integral must equal top.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.standing_nonGaussian_variation_or_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hσ : X.σ = 0) :
    (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤ ∨
      0 < X.drift := by sorry
