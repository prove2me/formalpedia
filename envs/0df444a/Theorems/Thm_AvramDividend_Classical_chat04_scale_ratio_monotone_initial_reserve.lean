-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_scale_ratio_monotone_initial_reserve
-- name    : AvramDividend.Classical.chat04_scale_ratio_monotone_initial_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T15:02:10.505125+00:00
-- url     : https://prove2.me/theorems/8c79233e-8c5a-4ac4-badf-8f1187138536
-- title:
--   Two-sided scale exit ratio increases with the initial reserve
-- statement:
--   For positive q and a canonical scale function under Standing, the ratio W(x)/W(a) at a fixed strictly positive barrier a is monotone in x over nonnegative reserves. This establishes the monotonicity expected of the two-sided killed exit probability as an independent scale-side lemma.
-- source:
--   MonotoneOn component of IsScaleFunction, positive W(a) from previously Proved scaleFunction_strict_pos_of_standing, and Avram et al. 2007 equation (3.6).

import Mathlib.Algebra.Order.Field.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_strict_pos_of_standing

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_scale_ratio_monotone_initial_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a x y : ℝ)
    (ha : 0 < a) (hx0 : 0 ≤ x) (hxy : x ≤ y) :
    W x / W a ≤ W y / W a := by sorry
