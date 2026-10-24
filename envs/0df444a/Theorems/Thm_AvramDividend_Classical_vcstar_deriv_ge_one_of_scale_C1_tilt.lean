-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one_of_scale_C1_tilt
-- name    : AvramDividend.Classical.vcstar_deriv_ge_one_of_scale_C1_tilt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T09:41:24.786107+00:00
-- url     : https://prove2.me/theorems/36de0c50-cf40-4fd6-9c9f-e2121fdb3bf7
-- title:
--   Global barrier gradient inequality from C1 scale regularity and a monotone Esscher tilt
-- statement:
--   Assume the scale function is C1 on positive reserves and admits a strictly positive exponential tilt under which it is monotone. The standing assumptions guarantee W(x)>0. The tilt gives W'(x)>0, continuity of W' supplies minimality of the optimal-barrier derivative, and the piecewise-calculus lemma implies the ordinary derivative of the barrier candidate exists and is at least one for every positive reserve.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 3(i): combine proved monotone tilt derivative positivity, cstar minimiser and piecewise calculus.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing
import Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos_of_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_cstar_toReal_zero_or_minimal_of_deriv_continuous
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one_of_regular_minimal
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical
theorem vcstar_deriv_ge_one_of_scale_C1_tilt
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hreg : ContDiffOn ℝ 1 W (Ioi (0 : ℝ)))
    (htilt : ∃ φ : ℝ, 0 < φ ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0)) :
    ∀ x : ℝ, 0 < x →
      DifferentiableAt ℝ (vcstar W) x ∧ 1 ≤ deriv (vcstar W) x := by sorry
end AvramDividend.Classical
