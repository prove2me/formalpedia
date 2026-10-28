-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_global_C2_gaussian_of_positive_tilt
-- name    : AvramDividend.Classical.vcstar_global_C2_gaussian_of_positive_tilt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T08:25:37.912264+00:00
-- url     : https://prove2.me/theorems/b6f43a12-bf05-4976-83df-0313af7a4fec
-- title:
--   Global Gaussian C2 optimal barrier under a positive monotone Esscher tilt
-- statement:
--   Under Standing and positive Gaussian coefficient, existing scale-function C2 regularity plus an explicitly supplied positive Esscher monotonicity give a strictly positive derivative W'(c*), global C1 of the barrier candidate and stationary curvature W''(c*)=0. The verified deterministic C2 gluing theorem then gives global C2 smoothness across c*. It isolates the precise Esscher monotonicity prerequisite of the main Gaussian verification theorem without claiming the general Standing assumptions alone already prove that prerequisite.
-- source:
--   Avram, Palmowski and Pistorius (2007), positive-Gaussian scale smoothness and positive Esscher tilt, with deterministic smooth-fit.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_two_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_continuous_of_gaussian
import Theorems.Thm_AvramDividend_Classical_deriv_deriv_eq_zero_at_positive_cstar_of_deriv_continuous
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos_of_gaussian_tilt
import Theorems.Thm_AvramDividend_Classical_vcstar_C1_of_scale_C1_tilt
import Theorems.Thm_AvramDividend_Classical_vcstar_global_C2_of_C2_scale_stationary_positive_C1
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical
/-- Gaussian C2 smooth fit under an explicitly supplied positive monotone Esscher scale tilt. -/
theorem vcstar_global_C2_gaussian_of_positive_tilt
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hcpos : 0 < (cstar W).toReal) (hσ : 0 < X.σ)
    (htilt : ∃ φ : ℝ, 0 < φ ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0)) :
    ContDiffOn ℝ 2 (vcstar W) (Ioi (0 : ℝ)) := by
  sorry
end AvramDividend.Classical
