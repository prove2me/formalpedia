-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_controlled_aggregate_loss_monotone
-- name    : AvramDividend.Classical.avram_wave3_03_bv_controlled_aggregate_loss_monotone
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T00:12:34.634133+00:00
-- url     : https://prove2.me/theorems/da963978-4186-4018-acdb-c2047563cda4
-- title:
--   Actual controlled BV reserve is physical drift minus a nondecreasing aggregate loss path
-- statement:
--   For any genuine bounded-variation spectrally negative Lévy process and any left-continuous monotone admissible dividend path, on a common probability-one event the residual t*d - (x+X_t-D_t) is nondecreasing simultaneously at all times. This exhibits the exact controlled path as physical drift minus a monotone sum of Lévy losses and all Stieltjes dividend payments, including continuous and singular-continuous control.
-- source:
--   The canonically Proved original Lévy residual monotonicity f6cc1059 combined with the actual riskProcess definition and nondecreasing dividend strategy; no purely atomic assumption or predictable compensation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave3_03_bv_controlled_aggregate_loss_monotone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) :
    ∀ᵐ ω ∂P,
      Monotone (fun t : ℝ≥0 => (t : ℝ) * X.drift - riskProcess X x D t ω) := by sorry
