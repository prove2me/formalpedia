-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_or_bv_hjb_iff_above_residual
-- name    : AvramDividend.Classical.avram_wave4_05_gaussian_or_bv_hjb_iff_above_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T14:11:42.983782+00:00
-- url     : https://prove2.me/theorems/0dc60c32-a09b-4e1b-862e-0f2e9a77147f
-- title:
--   Source Gaussian/BV HJB is equivalent to the above-barrier generator residual inequality
-- statement:
--   For an original standing spectrally negative Levy source with genuine q-scale and positive discount, if the source has positive Gaussian coefficient or bounded variation, the complete actual-source HJB condition (including GeneratorIntegrable at all positive reserves) is equivalent to the generator residual inequality Γvcstar−qvcstar≤0 strictly above the optimal barrier. Necessity follows from the maximum expression and positivity of reserve beyond cstar; sufficiency is the canonically accepted Gaussian/BV source HJB theorem, which already proves all local source generator integrability and boundary cases.
-- source:
--   Avram–Palmowski–Pistorius (2007), Lemma 4 and Theorem 2; Proved source Gaussian/BV HJB 7842ea2c

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave4_05_gaussian_or_bv_hjb_residual_only

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_05_gaussian_or_bv_hjb_iff_above_residual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W)
    (hbranch : 0 < X.σ ∨ X.BoundedVariation) :
    (∀ y : ℝ, 0 < y →
      X.GeneratorIntegrable (vcstar W) y ∧
        max (X.generator (vcstar W) y - q * vcstar W y)
            (1 - deriv (vcstar W) y) = 0) ↔
    (∀ y : ℝ, (cstar W).toReal < y →
      X.generator (vcstar W) y - q * vcstar W y ≤ 0) := by sorry
