-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleDeriv_inf_attained_of_corrected_exit_and_C1
-- name    : AvramDividend.Classical.scaleDeriv_inf_attained_of_corrected_exit_and_C1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:02:54.400284+00:00
-- url     : https://prove2.me/theorems/28d54129-a297-4a42-acf1-34c644e09c94
-- title:
--   Scale-derivative attained-infimum or zero-barrier dichotomy from corrected exits and C1 regularity
-- statement:
--   Suppose the corrected two-sided-exit identity holds for the spectrally negative Lévy process under Avram's standing conditions and its q-scale function is C1 on (0,infinity). Then the derivative either achieves its global minimum at a positive level or the right liminf at zero is no greater than any positive-axis derivative. This is the exact dichotomy needed to close the attained-infimum parent after Workstreams 1 and 2 establish their hypotheses.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 2(i), §5.3; canonical Proved Esscher-positive monotone from corrected exit, derivative-growth and deterministic minimum-or-boundary lemmas.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_corrected_exit
import Theorems.Thm_AvramDividend_Classical_scale_deriv_tendsto_atTop_of_normalized_monotone
import Theorems.Thm_AvramDividend_Classical_positive_minimum_or_right_liminf_of_tendsto_atTop
import Mathlib.Analysis.Calculus.Deriv.Basic

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleDeriv_inf_attained_of_corrected_exit_and_C1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a))
    (hreg : ContDiffOn ℝ 1 W (Ioi 0)) :
    (∃ a : ℝ, 0 < a ∧ ∀ x : ℝ, 0 < x → deriv W a ≤ deriv W x) ∨
      ∀ x : ℝ, 0 < x →
        derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal) := by sorry
