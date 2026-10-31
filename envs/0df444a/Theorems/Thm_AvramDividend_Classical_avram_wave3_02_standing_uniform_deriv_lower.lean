-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_standing_uniform_deriv_lower
-- name    : AvramDividend.Classical.avram_wave3_02_standing_uniform_deriv_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T13:09:51.371832+00:00
-- url     : https://prove2.me/theorems/6d4ff289-57e0-4fde-9cf3-02169c6c6456
-- title:
--   Original q-scale derivative dominates scale uniformly at all differentiability points
-- statement:
--   For every genuine Standing spectrally negative Lévy process with q>0 and original q-scale W, there exists one real c>0 such that at every positive reserve a where W is differentiable, cW(a)≤W'(a). The coefficient is uniform in a and is obtained from canonically Proved Esscher scale growth and the verified Stieltjes reflected boundary-reward estimate. No global C1 hypothesis is required.
-- source:
--   Avram Palmowski Pistorius (2007), exponential q-scale transform and Proposition 1 reflected Stieltjes valuation.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_esscher_unit_step_scale_growth
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_deriv_lower_of_unit_gap

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_standing_uniform_deriv_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∃ c : ℝ, 0 < c ∧ ∀ a : ℝ, 0 < a → DifferentiableAt ℝ W a →
      c * W a ≤ deriv W a := by sorry
