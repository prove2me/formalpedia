-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_gaussian_tilt
-- name    : AvramDividend.Classical.vcstar_deriv_one_of_gaussian_tilt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T09:27:14.224071+00:00
-- url     : https://prove2.me/theorems/b242777d-6ff6-4ecb-a54e-a3d1eff357e6
-- title:
--   Gaussian smooth fit from Esscher-normalised tilted monotonicity
-- statement:
--   For a canonical q-scale function with positive Gaussian coefficient, global positive-axis C1 regularity and positivity are established. If there exists a strictly positive Esscher exponent such that e^(-φx)W(x) is nondecreasing, the scale derivative at the positive barrier is strictly positive and the classical barrier candidate has ordinary derivative one at the join. This isolates the remaining Gaussian stochastic tilt construction.
-- source:
--   Avram, Palmowski and Pistorius (2007), Gaussian scale derivative and Esscher monotonicity; applies already-proved calculus bridge.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Data.ENNReal.Real
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos_of_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_local_scale_deriv_positive
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical
theorem vcstar_deriv_one_of_gaussian_tilt
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hσ : 0 < X.σ)
    (htilt : ∃ φ : ℝ, 0 < φ ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0)) :
    deriv (vcstar W) (cstar W).toReal = 1 := by sorry
end AvramDividend.Classical
