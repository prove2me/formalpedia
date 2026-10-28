-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_psi_discount_reciprocal_tendsto_zero
-- name    : AvramDividend.Classical.unbounded_psi_discount_reciprocal_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T10:15:53.097647+00:00
-- url     : https://prove2.me/theorems/03e77a7a-cc5e-46f0-ae71-a02beea42c14
-- title:
--   Normalised inverse discounted Lévy exponent tends to zero
-- statement:
--   For a spectrally negative Lévy process of unbounded variation and nonnegative discount rate, the real-valued function θ ↦ θ/(ψ(θ) − q) tends to zero as θ tends to positive infinity. This gives the filter-limit interface to the previously proved quantitative large-parameter reciprocal bound.
-- source:
--   A direct application of the order-topology criterion for real-valued limits to AvramDividend.Classical.unbounded_psi_discount_reciprocal_small, UUID d5c48916-f37f-4cca-ba7c-667717c96432.

import Mathlib.Topology.Order.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_psi_discount_reciprocal_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 ≤ q) :
    Tendsto (fun θ : ℝ => θ / (X.ψ θ - q)) atTop (nhds 0) := by sorry
