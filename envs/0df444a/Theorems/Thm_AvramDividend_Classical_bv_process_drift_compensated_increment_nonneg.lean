-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_process_drift_compensated_increment_nonneg
-- name    : AvramDividend.Classical.bv_process_drift_compensated_increment_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:58:11.183739+00:00
-- url     : https://prove2.me/theorems/0ff03099-99fe-46d7-bb83-c2ccb6e630ba
-- title:
--   Bounded variation gives nonnegative drift-compensated increments
-- statement:
--   For a bounded-variation spectrally negative Levy process, the fixed-time increment of S_t = X.drift*t - X.X t is nonnegative almost surely. Derive its Laplace transform from the exact exponent and show that a negative tail contradicts the transform bound.
-- source:
--   Necessary process reduction for AvramDividend.Classical.bounded_variation_stopped_scale_balance (target 2bb529c8-d611-4c49-9460-1d4af4620ae8): its exact bounded-variation exponent identity gives a nonnegative Laplace deficit, which forces each fixed increment of X.drift*t-X.X t to be nonnegative almost surely.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology
open AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_process_drift_compensated_increment_nonneg
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (s t : ℝ≥0) (hst : s ≤ t) :
    ∀ᵐ ω ∂P,
      0 ≤ X.drift * ((t : ℝ) - (s : ℝ)) - (X.X t ω - X.X s ω) := by sorry
