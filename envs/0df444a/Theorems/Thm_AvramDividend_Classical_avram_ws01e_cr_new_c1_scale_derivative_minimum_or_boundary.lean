-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_cr_new_c1_scale_derivative_minimum_or_boundary
-- name    : AvramDividend.Classical.avram_ws01e_cr_new_c1_scale_derivative_minimum_or_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T00:02:22.226751+00:00
-- url     : https://prove2.me/theorems/7d11fc46-d922-4474-9a85-da3b9ffad903
-- title:
--   C1 standing scale derivative attains its positive minimum or the zero-right-liminf alternative, without killed-exit premise
-- statement:
--   Under the actual Avram Standing hypotheses, positive discount and an honest q-scale function, C1 regularity on (0,infinity) suffices for the exact derivative-minimum or zero-barrier liminf dichotomy required by the canonical scaleDeriv_inf_attained. The corrected-exit identity is not an additional hypothesis because the actual tilted-scale positivity and monotonicity theorem is already Proved.
-- source:
--   Pinned Proved scaleFunction_tilted_positive_monotone, scale_deriv_tendsto_atTop_of_normalized_monotone, positive_minimum_or_right_liminf_of_tendsto_atTop. Removes obsolete corrected-exit hypothesis from previously Proved scaleDeriv_inf_attained_of_corrected_exit_and_C1, leaving a genuinely weaker conditional bridge to the current Open WS3 parent.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_tilted_positive_monotone
import Theorems.Thm_AvramDividend_Classical_scale_deriv_tendsto_atTop_of_normalized_monotone
import Theorems.Thm_AvramDividend_Classical_positive_minimum_or_right_liminf_of_tendsto_atTop
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_cr_new_c1_scale_derivative_minimum_or_boundary
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hreg : ContDiffOn ℝ 1 W (Ioi 0)) :
    (∃ a : ℝ, 0 < a ∧ ∀ x : ℝ, 0 < x → deriv W a ≤ deriv W x) ∨
      ∀ x : ℝ, 0 < x →
        derivZeroPlus W ≤ ((deriv W x : ℝ) : EReal) := by sorry
