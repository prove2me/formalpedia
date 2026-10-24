-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_tilt_monotone_of_corrected_exit_identity
-- name    : AvramDividend.Classical.gaussian_tilt_monotone_of_corrected_exit_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T15:33:06.602645+00:00
-- url     : https://prove2.me/theorems/c4bc6f66-18da-41fa-a350-02d7f19603c5
-- title:
--   Gaussian Esscher-scale monotonicity from the corrected two-sided exit identity alone
-- statement:
--   For the canonical q-scale function of a spectrally negative Lévy process with positive Gaussian coefficient, the corrected killed two-sided exit identity implies that there exists a positive Esscher root making the exponentially normalised scale function monotone on the positive axis. The independent stopped exponential bound is already proved, so no separate exponential estimate is hypothesised.
-- source:
--   Avram, Palmowski and Pistorius (2007), positive Esscher scale comparison and two-sided exit identity; Prove2Me corrected stopped-exponential bound.

import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_corrected_exit_exp_bound_at_positive_root
import Theorems.Thm_AvramDividend_Classical_corrected_exit_bound_gaussian_tilted

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical
theorem gaussian_tilt_monotone_of_corrected_exit_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q ∧
      MonotoneOn (fun x : ℝ => Real.exp (-φ * x) * W x) (Ioi 0) := by sorry
end AvramDividend.Classical
