-- Prove2me | Theorems.Thm_AvramDividend_Classical_hjb_pointwise_inequalities
-- name    : AvramDividend.Classical.hjb_pointwise_inequalities
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T09:56:14.811816+00:00
-- url     : https://prove2.me/theorems/1f53c151-a506-4b78-af1d-3584388f1979
-- title:
--   Pointwise generator and marginal-dividend inequalities from the HJB maximum
-- statement:
--   The HJB equality max{Γw-qw, 1-w'}=0 implies separately Γw-qw≤0 and w'≥1. These are the two inequalities used in the stopped Itô/change-of-variable verification estimate for Proposition 4(i).
-- source:
--   Avram, Palmowski, Pistorius (2007), Eq. (5.8), p. 17, split into its two pointwise inequalities for the proof of Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.hjb_pointwise_inequalities
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (w : ℝ → ℝ) (y : ℝ)
    (hmax : max (X.generator w y - q * w y) (1 - deriv w y) = 0) :
    X.generator w y - q * w y ≤ 0 ∧ 1 ≤ deriv w y := by sorry
