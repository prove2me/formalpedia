-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_frozen_stieltjes_tail_zero
-- name    : AvramDividend.Classical.avram_wave3_03_bv_postPayment_frozen_stieltjes_tail_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T21:49:39.374543+00:00
-- url     : https://prove2.me/theorems/1ba0da17-3fd8-40ce-ac27-1a910f11dbbc
-- title:
--   Original BV post-payment frozen test has no Stieltjes mass beyond its horizon
-- statement:
--   For any finite horizon and every genuine BV controlled Levy reserve, the globally Lipschitz test of its post-payment reserve frozen at the horizon yields a BV path whose signed Stieltjes vector measure has zero mass on the strict tail after the horizon. The undiscounted path is genuinely constant there.
-- source:
--   Proved original BV post-payment global variation theorem and pinned vectorMeasure_Ioi plus one-sided limits of an eventually constant path.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_postPayment_truncated_global_variation
open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_bv_postPayment_frozen_stieltjes_tail_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (v : ℝ → ℝ) (L : NNReal) (hv : LipschitzWith L v) :
    ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      let g : ℝ≥0 → ℝ := fun t =>
        v (x + X.X (min t T) ω - rightLimit D (min t T) ω)
      ∃ hg : BoundedVariationOn g Set.univ,
        hg.vectorMeasure (Ioi T) = 0 := by sorry
