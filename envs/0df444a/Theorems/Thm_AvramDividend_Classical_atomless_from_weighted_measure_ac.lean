-- Prove2me | Theorems.Thm_AvramDividend_Classical_atomless_from_weighted_measure_ac
-- name    : AvramDividend.Classical.atomless_from_weighted_measure_ac
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T08:05:30.693175+00:00
-- url     : https://prove2.me/theorems/40d18dd0-bdb8-497e-96f7-d4dd00c207e9
-- title:
--   Nonnegative-support measure is atomless when its x-weighted measure is Lebesgue-AC and the zero atom vanishes
-- statement:
--   Let μ be a measure supported on [0,∞), with μ{0}=0, and assume the ENNReal x-weighted measure withDensity μ (ofReal x) is absolutely continuous with respect to Lebesgue volume. Then μ has no atoms at any real x. For x>0, the singleton formula for withDensity gives x μ{x}=0, and x>0 forces μ{x}=0; for x≤0 use support and the explicit zero-atom premise. This independent measure-theoretic lemma is the last step of the proposed Laplace-derivative convolution argument for the pure-jump renewal potential.
-- source:
--   Pinned Mathlib withDensity_apply, lintegral_singleton, mul_eq_zero, volume singleton null; target renewal atomlessness 2fa29eaf via U weighted Laplace convolution identity.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.atomless_from_weighted_measure_ac
    (μ : Measure ℝ) (hSupport : μ (Iio (0 : ℝ)) = 0)
    (hAtZero : μ {(0 : ℝ)} = 0)
    (hWeighted : (μ.withDensity (fun x : ℝ => ENNReal.ofReal x))
        ≪ (volume : Measure ℝ)) :
    ∀ x : ℝ, μ {x} = 0 := by sorry
