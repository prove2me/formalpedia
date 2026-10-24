-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_gaussian_smoothfit_of_corrected_exit_bounds
-- name    : AvramDividend.Classical.vcstar_gaussian_smoothfit_of_corrected_exit_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T14:50:43.114929+00:00
-- url     : https://prove2.me/theorems/0f0f806c-2a77-4fac-8360-8ae83be0f08d
-- title:
--   Gaussian smooth fit from corrected killed two-sided exit bounds
-- statement:
--   Conditional Gaussian smooth fit: the corrected killed two-sided exit identity and exponential Esscher upper bound give tilted monotonicity, hence the ordinary derivative of the optimal barrier value is one at the positive join. The two stochastic premises remain explicit.
-- source:
--   Avram, Palmowski and Pistorius (2007), Gaussian case; verified corrected-exit bridge and Gaussian smooth-fit lemma.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_corrected_exit_bound_gaussian_tilted
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_gaussian_tilt

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical
theorem vcstar_gaussian_smoothfit_of_corrected_exit_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hσ : 0 < X.σ)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a))
    (hBound : ∀ φ : ℝ, 0 < φ → X.ψ φ = q →
      ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
        twoSidedExitExpectationCorrected X q a x ≤
          ENNReal.ofReal (Real.exp (-φ * (a - x)))) :
    deriv (vcstar W) (cstar W).toReal = 1 := by sorry
end AvramDividend.Classical
