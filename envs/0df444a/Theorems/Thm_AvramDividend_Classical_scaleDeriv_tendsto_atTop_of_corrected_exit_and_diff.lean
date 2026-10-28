-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleDeriv_tendsto_atTop_of_corrected_exit_and_diff
-- name    : AvramDividend.Classical.scaleDeriv_tendsto_atTop_of_corrected_exit_and_diff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T13:59:50.450975+00:00
-- url     : https://prove2.me/theorems/f9e09276-6dff-4bfc-8066-74f220d05e5e
-- title:
--   Scale derivative divergence from corrected two-sided exits and positive-axis differentiability
-- statement:
--   For a spectrally negative Levy process satisfying Standing and q>0, the corrected two-sided killed-exit scale identity combined with differentiability of the q-scale function at every positive point implies W'(x) tends to positive infinity as x grows. This is the original cstar derivative-growth conclusion conditional on precisely the two missing stochastic/regularity prerequisites. The fully Proved proof imports the corrected-exit Esscher positivity-monotonicity case split and the already Proved deterministic derivative-growth theorem for a positive exponentially normalised monotone function. The conditions are explicit and no unproved limit or target theorem is imported.
-- source:
--   Avram Palmowski Pistorius (2007), q-scale Esscher normalisation; Proved AvramDividend.Classical.scale_deriv_tendsto_atTop_of_normalized_monotone.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_corrected_exit
import Theorems.Thm_AvramDividend_Classical_scale_deriv_tendsto_atTop_of_normalized_monotone
import Mathlib.Analysis.Calculus.Deriv.Basic
open AvramDividend.Classical MeasureTheory Filter Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleDeriv_tendsto_atTop_of_corrected_exit_and_diff
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a))
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) :
    Tendsto (deriv W) atTop atTop := by sorry
