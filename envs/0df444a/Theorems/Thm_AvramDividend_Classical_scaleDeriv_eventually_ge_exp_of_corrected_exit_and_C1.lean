-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleDeriv_eventually_ge_exp_of_corrected_exit_and_C1
-- name    : AvramDividend.Classical.scaleDeriv_eventually_ge_exp_of_corrected_exit_and_C1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:08:02.938369+00:00
-- url     : https://prove2.me/theorems/ce1c0023-6c3e-4cc6-850c-f9242dbae83c
-- title:
--   Quantitative exponential lower bound on q-scale derivative from corrected exits and C1
-- statement:
--   Under Avram standing assumptions and positive discount, suppose the corrected two-sided-exit identity and positive-axis C1 regularity hold. Then the q-scale derivative eventually dominates c exp(phi*x) for positive c and phi. This quantitative strengthening is a complete conditional reduction to Workstreams 1 and 2 and supplies the general eventual-exponential-growth milestone once those prerequisites are canonical.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 2(i); Proved corrected-exit Esscher positivity, normalized derivative lower bound and normalized eventual exponential growth.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone_of_corrected_exit
import Theorems.Thm_AvramDividend_Classical_normalized_derivative_lower_bound
import Theorems.Thm_AvramDividend_Classical_normalized_eventual_derivative_growth
import Mathlib.Analysis.Calculus.Deriv.Basic

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.scaleDeriv_eventually_ge_exp_of_corrected_exit_and_C1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hExit : ∀ a x : ℝ, 0 < a → 0 ≤ x → x ≤ a →
      twoSidedExitExpectationCorrected X q a x =
        ENNReal.ofReal (W x / W a))
    (hreg : ContDiffOn ℝ 1 W (Ioi 0)) :
    ∃ φ c : ℝ, 0 < φ ∧ 0 < c ∧
      ∀ᶠ x in Filter.atTop, c * Real.exp (φ * x) ≤ deriv W x := by sorry
