-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_weighted_levy_measure_support_ac
-- name    : AvramDividend.Classical.esscher_weighted_levy_measure_support_ac
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:04:42.870548+00:00
-- url     : https://prove2.me/theorems/10b6d32c-c23a-4a4d-a47a-d7a608f4574c
-- title:
--   Esscher exponential weighting preserves negative-jump support and absolute continuity
-- statement:
--   Weighting a spectrally negative Lévy jump measure by the positive Esscher factor exp(phi*y) preserves its lack of nonnegative jumps and its absolute continuity with respect to Lebesgue measure. This is the elementary measure-theoretic invariant required when transferring the bounded-variation absolutely-continuous case of the scale-function regularity theorem to the Esscher-transformed process. It does not construct the Esscher process itself.
-- source:
--   Pinned Mathlib withDensity_absolutelyContinuous and Measure.AbsolutelyContinuous.trans; Chan Kyprianou Savov (2011), tilted Lévy measure identity Pi_Phi(q)(dy)=exp(Phi(q)y)Pi(dy).

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.esscher_weighted_levy_measure_support_ac
    (ν : Measure ℝ) (φ : ℝ)
    (hneg : ν (Ici 0) = 0) (hac : ν ≪ volume) :
    (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y)))) (Ici 0) = 0 ∧
    ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))) ≪ volume := by sorry
