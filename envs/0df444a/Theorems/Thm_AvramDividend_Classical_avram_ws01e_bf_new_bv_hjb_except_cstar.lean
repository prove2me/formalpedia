-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_bv_hjb_except_cstar
-- name    : AvramDividend.Classical.avram_ws01e_bf_new_bv_hjb_except_cstar
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:10:51.25274+00:00
-- url     : https://prove2.me/theorems/857d1aba-414b-4d74-aa8e-e74c27d70307
-- title:
--   Bounded-variation optimal dividend HJB identity at every positive reserve away from cstar
-- statement:
--   For a standing spectrally negative Levy process of bounded variation and q>0, if the exact candidate barrier value satisfies the original above-barrier generator inequality, then the full nonlocal HJB equation and generator integrability hold for every positive reserve other than exactly the barrier. The already Proved genuine BV interior harmonicity supplies the below-barrier case. The already Proved affine-above-barrier identity supplies the upper case. The only remaining single-point issue for the fully global theorem is the generator value at a strictly positive barrier.
-- source:
--   Source-faithful conditional bounded-variation bridge toward AvramDividend.Classical.vcstar_hjb_all_positive_of_generator (edf09308). Its stochastic below-barrier input is the Proved actual BV theorem 2af73322 and its above-barrier input is the Proved generator inequality bridge e1d50a0b. No additional independence or generator harmonisation assumption is introduced below the barrier.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_below_positive_cstar_bv_20261027
import Theorems.Thm_AvramDividend_Classical_vcstar_hjb_above_cstar_of_generator
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bf_new_bv_hjb_except_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation)
    (hgen : ∀ y : ℝ, (cstar W).toReal < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        X.generator (vcstar W) y - q * vcstar W y ≤ 0) :
    ∀ y : ℝ, 0 < y → y ≠ (cstar W).toReal →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0 := by sorry
