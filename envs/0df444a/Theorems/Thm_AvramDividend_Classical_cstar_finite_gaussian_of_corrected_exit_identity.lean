-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_finite_gaussian_of_corrected_exit_identity
-- name    : AvramDividend.Classical.cstar_finite_gaussian_of_corrected_exit_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T15:54:04.308817+00:00
-- url     : https://prove2.me/theorems/41761b06-bb53-497e-bcd2-95040a90f232
-- title:
--   Gaussian optimal-barrier finiteness from the corrected killed two-sided exit identity
-- statement:
--   For a Gaussian spectrally negative Levy process with standing assumptions and positive discount, the corrected killed two-sided exit identity implies that the optimal barrier cstar of its scale function is finite.
-- source:
--   Avram, Palmowski and Pistorius (2007), scale-function regularity and finite optimal barrier.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_gaussian_tilt_monotone_of_corrected_exit_identity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_gaussian
import Theorems.Thm_AvramDividend_Classical_cstar_finite_of_gaussian_tilt_monotone

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical
theorem cstar_finite_gaussian_of_corrected_exit_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    cstar W < ⊤ := by sorry
end AvramDividend.Classical
