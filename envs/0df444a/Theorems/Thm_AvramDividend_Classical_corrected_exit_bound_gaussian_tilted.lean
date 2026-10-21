-- Prove2me | Theorems.Thm_AvramDividend_Classical_corrected_exit_bound_gaussian_tilted
-- name    : AvramDividend.Classical.corrected_exit_bound_gaussian_tilted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T20:35:19.420074+00:00
-- url     : https://prove2.me/theorems/9b5cd714-34bf-4a82-bdfe-926a0aac970f
-- title:
--   Corrected killed two-sided exit identity and exponential bound yield Gaussian tilted-scale monotonicity
-- statement:
--   For a nonzero-Gaussian spectrally negative Lévy process and canonical q-scale function, the official corrected two-sided exit expectation, if equal to ENNReal.ofReal(W(x)/W(a)) and bounded by ENNReal.ofReal(exp(-φ(a-x))) at every positive root φ and 0<x≤a, implies existence of the root and monotonicity of exp(-φx)W(x). This proves the precise ENNReal-to-real ratio conversion using the pinned ENNReal.ofReal_le_ofReal_iff and separately accepted Gaussian positivity and ratio-to-tilt theorems. Both substantive stochastic premises remain explicit.
-- source:
--   Proved scaleFunction_strict_pos_of_gaussian, gaussian_ratio_bound_tilted_monotone and pinned Mathlib ENNReal.ofReal_le_ofReal_iff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.corrected_exit_bound_gaussian_tilted
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
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
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by sorry
