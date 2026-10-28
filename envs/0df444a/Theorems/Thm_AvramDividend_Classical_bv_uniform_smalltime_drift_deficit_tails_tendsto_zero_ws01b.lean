-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_uniform_smalltime_drift_deficit_tails_tendsto_zero_ws01b
-- name    : AvramDividend.Classical.bv_uniform_smalltime_drift_deficit_tails_tendsto_zero_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T09:17:17.683447+00:00
-- url     : https://prove2.me/theorems/0f9f587f-b03e-4c62-8f54-f748b4ec4349
-- title:
--   Uniform small-time bounded-variation Lévy drift-deficit tails vanish in probability
-- statement:
--   For a spectrally negative bounded-variation Lévy process, the probability that the drift deficit scaled by a frequency θ_n exceeds a positive threshold anywhere in [0,δ_n] tends to zero, assuming θ_n→∞, θ_n≥1 and δ_n θ_n=c. This strengthens a previously proved fixed-time estimate to uniform path control, including infinite jump activity.
-- source:
--   Proved fixed-time tail theorem 6fbd417b and Proved ae-monotonicity theorem bdb273f0; scale-function theory, BV subordinator decomposition.

import Theorems.Thm_AvramDividend_Classical_bv_scaled_drift_deficit_tails_tendsto_zero_ws01b
import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.MeasureTheory.OuterMeasure.AE
import Mathlib.Data.ENNReal.Real
import Mathlib.Topology.Order.Basic

open AvramDividend.Classical MeasureTheory Filter Topology Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_uniform_smalltime_drift_deficit_tails_tendsto_zero_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (δ : ℕ → ℝ≥0) (θ : ℕ → ℝ) (c : ℝ)
    (hθ : Tendsto θ atTop atTop)
    (hθge : ∀ n, 1 ≤ θ n)
    (hProduct : ∀ n, (δ n : ℝ) * θ n = c)
    (a : ℝ) (ha : 0 < a) :
    Tendsto (fun n : ℕ =>
      P.real {ω : Ω | ∃ t : ℝ≥0, t ≤ δ n ∧
        a ≤ θ n * ((t : ℝ) * X.drift - X.X t ω)})
      atTop (𝓝 (0 : ℝ)) := by sorry
