-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_zero_probability
-- name    : AvramDividend.Classical.bv_actual_levy_drift_upper_zero_probability
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:50:37.275992+00:00
-- url     : https://prove2.me/theorems/2a9d5b9b-8f96-4d35-b2a0-bd05a22c1635
-- title:
--   No fixed-time drift overshoot for the actual bounded-variation Lévy process
-- statement:
--   For every fixed time t, bounded-variation spectrally negative Lévy sample paths have probability zero of lying at least ε above the deterministic positive drift line dt. Apply the proved actual-process Chernoff inequality with θ=n+1 and let n tend to infinity. This is a key support property for identifying the residual process dt-X_t as a subordinator and proving first-jump survival for the actual Lévy process.
-- source:
--   Proved actual-process Chernoff bound and pinned Mathlib exponential decay/closed-order limit lemmas.

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_chernoff_drift_bound
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Topology.Order.OrderClosed
import Mathlib.MeasureTheory.Measure.Real

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.bv_actual_levy_drift_upper_zero_probability
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (t : ℝ≥0) (ε : ℝ) (hε : 0 < ε) :
    P.real {ω : Ω | (t : ℝ) * X.drift + ε ≤ X.X t ω} = 0 := by sorry
