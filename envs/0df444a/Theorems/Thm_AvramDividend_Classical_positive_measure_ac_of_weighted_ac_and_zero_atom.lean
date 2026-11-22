-- Prove2me | Theorems.Thm_AvramDividend_Classical_positive_measure_ac_of_weighted_ac_and_zero_atom
-- name    : AvramDividend.Classical.positive_measure_ac_of_weighted_ac_and_zero_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T15:40:47.717357+00:00
-- url     : https://prove2.me/theorems/fa56301b-5b01-48a3-bbfd-961fd86d24a6
-- title:
--   Absolute continuity of nonnegative measure from x-weighted absolute continuity and zero atom
-- statement:
--   A nonnegative-supported measure U with no atom at zero is absolutely continuous with respect to Lebesgue measure if the measure with density x relative to U is Lebesgue absolutely continuous. On x>0 the weight x is strictly positive and cannot annihilate any U-null property; the only weight-zero point x=0 has zero U-mass by assumption. This is the measure-theoretic converse to the standard withDensity absolute-continuity lemma, used to upgrade weighted potential regularity to full potential density.
-- source:
--   Pinned Mathlib withDensity_apply, withDensity_eq_zero_iff, AE conditions and measure restriction; Proved 40d18dd0 gives atomic consequence, child of regularity 8c56d3e5.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.positive_measure_ac_of_weighted_ac_and_zero_atom (U : Measure ℝ)
    (hSupport : U (Iio (0 : ℝ)) = 0)
    (hZero : U {(0 : ℝ)} = 0)
    (hWeighted : (U.withDensity (fun x : ℝ => ENNReal.ofReal x)) ≪
      (volume : Measure ℝ)) :
    U ≪ (volume : Measure ℝ) := by sorry
