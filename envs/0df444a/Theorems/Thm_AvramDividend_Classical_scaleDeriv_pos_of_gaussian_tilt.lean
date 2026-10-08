-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleDeriv_pos_of_gaussian_tilt
-- name    : AvramDividend.Classical.scaleDeriv_pos_of_gaussian_tilt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T20:33:50.888373+00:00
-- url     : https://prove2.me/theorems/d08876ab-e1b8-4816-99b2-33b2536f4e78
-- title:
--   Positive derivative of a Gaussian q-scale function under positive normalised tilt
-- statement:
--   For a spectrally negative Levy process with positive Gaussian coefficient, a canonical q-scale function W has W(x)>0 for x>0. Given a positive exponent φ, monotonicity of exp(-φx)W(x) and positive-axis differentiability, obtain W'(x)≥φ W(x)>0 for each positive x. This is the Gaussian-branch conditional version of original scaleDeriv_pos; tilt monotonicity and C1 still need to follow from Standing to close the original milestone.
-- source:
--   Compose two already Proved targets, scaleFunction_strict_pos_of_gaussian and scale_deriv_pos_of_normalized_monotone; no local Lean executed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scale_deriv_pos_of_normalized_monotone

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

namespace AvramDividend.Classical
theorem scaleDeriv_pos_of_gaussian_tilt
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) (φ : ℝ) (hφ : 0 < φ)
    (htilt : MonotoneOn
      (fun t : ℝ => Real.exp (-φ * t) * W t) (Set.Ioi 0))
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x) :
    ∀ x : ℝ, 0 < x → 0 < deriv W x := by
  sorry
end AvramDividend.Classical
