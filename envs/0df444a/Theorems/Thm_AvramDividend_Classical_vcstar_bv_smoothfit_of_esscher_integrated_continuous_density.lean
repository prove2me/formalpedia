-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_bv_smoothfit_of_esscher_integrated_continuous_density
-- name    : AvramDividend.Classical.vcstar_bv_smoothfit_of_esscher_integrated_continuous_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:26:30.244994+00:00
-- url     : https://prove2.me/theorems/8d676cb4-858a-4531-9372-73733b17f72a
-- title:
--   BV optimal-barrier smooth fit from a continuous Esscher-renewal density
-- statement:
--   In the bounded-variation standing Lévy case, a continuous interval-integrable Esscher-renewal density representation of the q-scale function suffices for the ordinary derivative of the cstar barrier value at the positive join to equal one. This isolates a density continuity and renewal representation obligation without asking for C2 regularity.
-- source:
--   Avram, Palmowski and Pistorius (2007), bounded-variation q-scale smooth fit, plus pinned Prove2Me positive-axis C1 and BV derivative-pasting lemmas.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_const_add_intervalIntegral
import Theorems.Thm_AvramDividend_Classical_esscher_untilt_contDiffOn_one_of_tilt_contDiffOn_one
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_one_of_bv_contDiff_one

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

namespace AvramDividend.Classical
theorem vcstar_bv_smoothfit_of_esscher_integrated_continuous_density
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W f : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (hbv : X.BoundedVariation)
    (φ c : ℝ)
    (hcont : ContinuousOn f (Ioi (0 : ℝ)))
    (hint : ∀ x : ℝ, 0 < x → IntervalIntegrable f volume 0 x)
    (hrepr : ∀ x : ℝ, 0 < x →
      Real.exp (-(φ * x)) * W x =
        c + ∫ y in (0 : ℝ)..x, f y) :
    deriv (vcstar W) (cstar W).toReal = 1 := by sorry
end AvramDividend.Classical
