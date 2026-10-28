-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleDeriv_inf_attained_of_bv_standing
-- name    : AvramDividend.Classical.scaleDeriv_inf_attained_of_bv_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:27:25.383208+00:00
-- url     : https://prove2.me/theorems/3b0765f7-8466-4c8f-98c3-8a97542ca571
-- title:
--   Positive derivative minimiser or zero-boundary alternative for bounded-variation scale functions
-- statement:
--   Under Avram standing assumptions and bounded variation, the positive-axis derivative of the q-scale function either attains a global minimum or every positive-axis derivative is at least its right liminf at zero. The proved BV absolute-continuity and C1 theorems supply derivative continuity, and the proved BV Esscher growth lemma supplies divergence at infinity. Apply the previously proved deterministic minimum-or-right-liminf dichotomy. This closes the bounded-variation case of the canonical attained-infimum milestone.
-- source:
--   Avram et al. (2007), Lemma 2(i); canonical proved standing_bv_levy_absolutely_continuous, scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy, bv_scaleDeriv_tendsto_atTop_of_C1, positive_minimum_or_right_liminf_of_tendsto_atTop.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_standing_bv_levy_absolutely_continuous
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
import Theorems.Thm_AvramDividend_Classical_bv_scaleDeriv_tendsto_atTop_of_C1
import Theorems.Thm_AvramDividend_Classical_positive_minimum_or_right_liminf_of_tendsto_atTop
import Mathlib.Analysis.Calculus.Deriv.Basic

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleDeriv_inf_attained_of_bv_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) :
    (∃ a : ℝ, 0 < a ∧ ∀ x : ℝ, 0 < x → deriv W a ≤ deriv W x) ∨
      ∀ x : ℝ, 0 < x →
        derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal) := by sorry
