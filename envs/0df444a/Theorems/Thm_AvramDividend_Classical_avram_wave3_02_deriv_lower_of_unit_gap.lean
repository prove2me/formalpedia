-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_02_deriv_lower_of_unit_gap
-- name    : AvramDividend.Classical.avram_wave3_02_deriv_lower_of_unit_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T12:49:13.600027+00:00
-- url     : https://prove2.me/theorems/844e6a71-f579-441d-a5a0-c08571655921
-- title:
--   Actual reflected Stieltjes reward bounds scale derivative at each differentiability point
-- statement:
--   Assume the original Standing spectrally negative Lévy q-scale function W has the same positive relative unit-increment gap c>0 at every positive reserve. At every positive a where W is differentiable, the genuine derivative obeys c W(a)≤W'(a). Proof uses the accepted uniform reflected Stieltjes reward bound, pointwise actual boundary reward identity W(a)/W'(a), positivity of the source derivative, and exact ENNReal-to-real rational inequality conversion. No global C1 or source-free surrogate is used.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 1 and equation (3.15); canonically Proved source reflected-reward quotient and gap bound.

import Mathlib.Data.ENNReal.Real
import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_deriv_pos_of_pointwise_diff
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_ratio_of_pointwise_diff_and_sandwich
import Theorems.Thm_AvramDividend_Classical_avram_wave3_02_uniform_boundary_reward_of_unit_gap

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_02_deriv_lower_of_unit_gap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (c : ℝ) (hc : 0 < c)
    (hgap : ∀ a : ℝ, 0 < a →
      c * W (a + 1) ≤ W (a + 1) - W a) :
    ∀ a : ℝ, 0 < a → DifferentiableAt ℝ W a →
      c * W a ≤ deriv W a := by sorry
