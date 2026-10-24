-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_bv_global_C1_of_esscher_integrated_continuous_density
-- name    : AvramDividend.Classical.vcstar_bv_global_C1_of_esscher_integrated_continuous_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:26:18.215417+00:00
-- url     : https://prove2.me/theorems/38025122-0ab7-4b33-b616-08cb42f4c396
-- title:
--   Global BV barrier C1 from a continuous Esscher-renewal density
-- statement:
--   For a standing bounded-variation spectrally negative Lévy process with a positive optimal barrier, an integral representation of the Esscher-tilted q-scale function with continuous density is sufficient to make the entire positive-axis cstar barrier value continuously differentiable. This is the regularity required by the BV branch of the optimal-barrier theorem.
-- source:
--   Avram, Palmowski and Pistorius (2007), BV smooth fit, plus already proved Prove2Me calculus, Esscher tilted monotonicity, and global barrier C1 lemmas.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_contDiffOn_one_const_add_intervalIntegral
import Theorems.Thm_AvramDividend_Classical_esscher_untilt_contDiffOn_one_of_tilt_contDiffOn_one
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_bv
import Theorems.Thm_AvramDividend_Classical_vcstar_C1_of_scale_C1_tilt

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

namespace AvramDividend.Classical
theorem vcstar_bv_global_C1_of_esscher_integrated_continuous_density
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W f : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hcpos : 0 < (cstar W).toReal)
    (φ c : ℝ)
    (hcont : ContinuousOn f (Ioi (0 : ℝ)))
    (hint : ∀ x : ℝ, 0 < x → IntervalIntegrable f volume 0 x)
    (hrepr : ∀ x : ℝ, 0 < x →
      Real.exp (-(φ * x)) * W x =
        c + ∫ y in (0 : ℝ)..x, f y) :
    ContDiffOn ℝ 1 (vcstar W) (Ioi (0 : ℝ)) := by sorry
end AvramDividend.Classical
