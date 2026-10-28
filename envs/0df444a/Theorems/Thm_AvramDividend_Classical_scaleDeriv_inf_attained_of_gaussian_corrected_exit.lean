-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleDeriv_inf_attained_of_gaussian_corrected_exit
-- name    : AvramDividend.Classical.scaleDeriv_inf_attained_of_gaussian_corrected_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:57:20.170092+00:00
-- url     : https://prove2.me/theorems/be8350fb-daef-4c07-9652-cfad5063fc66
-- title:
--   Gaussian derivative-minimum dichotomy conditional on the corrected two-sided-exit identity
-- statement:
--   Let a spectrally negative Lévy process have a strictly positive Gaussian coefficient and a positive discount q. Conditional on the corrected killed two-sided-exit identity, the derivative of its q-scale function either attains a global minimum on the strictly positive axis or every positive-axis derivative exceeds its right lower limit at zero. The proof composes existing Proved Gaussian smoothness, positivity, tilted monotonicity and deterministic compactness lemmas. It does not assume the universal exit identity or Standing.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 2(i); canonical Proved gaussian_tilt_monotone_of_corrected_exit_identity, Gaussian C1, scale_deriv_tendsto_atTop_of_normalized_monotone, and positive_minimum_or_right_liminf_of_tendsto_atTop.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_gaussian_without_standing
import Theorems.Thm_AvramDividend_Classical_gaussian_tilt_monotone_of_corrected_exit_identity
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scale_deriv_tendsto_atTop_of_normalized_monotone
import Theorems.Thm_AvramDividend_Classical_positive_minimum_or_right_liminf_of_tendsto_atTop
import Mathlib.Analysis.Calculus.Deriv.Basic

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleDeriv_inf_attained_of_gaussian_corrected_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ)
    (hExit : ∀ a x : ℝ, 0 < a → 0 < x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a)) :
    (∃ a : ℝ, 0 < a ∧ ∀ x : ℝ, 0 < x → deriv W a ≤ deriv W x) ∨
      ∀ x : ℝ, 0 < x →
        derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal) := by sorry
