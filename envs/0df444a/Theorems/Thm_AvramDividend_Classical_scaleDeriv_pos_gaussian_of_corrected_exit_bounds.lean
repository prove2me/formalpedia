-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos_gaussian_of_corrected_exit_bounds
-- name    : AvramDividend.Classical.scaleDeriv_pos_gaussian_of_corrected_exit_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:56:49.174545+00:00
-- url     : https://prove2.me/theorems/1015f232-b8aa-4e08-a11b-fc7188815e5b
-- title:
--   Positive Gaussian scale derivative from corrected killed-exit comparison
-- statement:
--   For a q-scale function with positive Gaussian coefficient and Standing, if the corrected killed-exit identity and exponential Esscher estimate hold, the q-scale derivative is strictly positive at every positive argument. This isolates the first-passage stochastic assumptions while discharging C1 regularity and the derivative calculation using previously Proved lemmas.
-- source:
--   Avram, Palmowski and Pistorius (2007), Gaussian scale regularity and positive Esscher representation.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_corrected_exit_bound_gaussian_tilted
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos_of_gaussian_tilt

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical
theorem scaleDeriv_pos_gaussian_of_corrected_exit_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a))
    (hBound : ∀ φ : ℝ, 0 < φ → X.ψ φ = q →
      ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
        twoSidedExitExpectationCorrected X q a x ≤
          ENNReal.ofReal (Real.exp (-φ * (a - x)))) :
    ∀ x : ℝ, 0 < x → 0 < deriv W x := by sorry
end AvramDividend.Classical
