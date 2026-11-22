-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_weight_retains_infinite_origin_mass
-- name    : AvramDividend.Classical.esscher_weight_retains_infinite_origin_mass
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T15:24:09.691196+00:00
-- url     : https://prove2.me/theorems/011d0df2-6ebd-479e-804b-eb216798cbf0
-- title:
--   Esscher weighting preserves infinite jump-tail mass near the origin
-- statement:
--   A measure with infinite mass on positive magnitudes t∈(0,1] retains infinite mass there after multiplication by the strictly positive bounded-below Esscher factor exp(−φt), φ≥0. The density is uniformly at least exp(−φ)>0 on (0,1]. This establishes the infinite-activity, zero-atom-at-origin condition in the genuine purejump UBV killed ladder-height renewal potential construction; no finite first jump moment is assumed.
-- source:
--   Pinned Mathlib lintegral_const, withDensity_apply, lintegral_mono_ae, ENNReal positivity. Original ψ/θ tail source 0fded7ba and original UBV infinite tail mass 8f9e6281 are Proved.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_weight_retains_infinite_origin_mass (μ : Measure ℝ)
    (φ : ℝ) (hφ : 0 ≤ φ)
    (hinf : μ (Ioc (0 : ℝ) 1) = ⊤) :
    (μ.withDensity (fun t : ℝ =>
      ENNReal.ofReal (Real.exp (-(φ * t))))) (Ioc (0 : ℝ) 1) = ⊤ := by sorry
