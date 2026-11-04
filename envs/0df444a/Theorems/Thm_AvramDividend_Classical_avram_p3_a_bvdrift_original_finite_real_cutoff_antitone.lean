-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_finite_real_cutoff_antitone
-- name    : AvramDividend.Classical.avram_p3_a_bvdrift_original_finite_real_cutoff_antitone
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:40:38.831+00:00
-- url     : https://prove2.me/theorems/fa6dcf8b-04e0-4dfe-922a-7a17f5f7ab04
-- title:
--   Original BV finite real negative-jump cutoff totals are antitone in threshold
-- statement:
--   On one full-measure event for the original bounded-variation spectrally negative Lévy source, for every horizon and every two ENNReal thresholds epsilon1≤epsilon2, both real conversions of the genuine jump cutoff totals are finite and the larger-threshold total is bounded by the smaller-threshold total. No Poisson representation or compensator assumption.
-- source:
--   Original source interval BV total finiteness e80cd41a; accepted source cutoff antitonicity d3c31092; pointwise ENNReal cutoff domination; pinned ENNReal.toReal_mono with finite majorant.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_interval_negative_jump_tsum_lt_top
import Theorems.Thm_AvramDividend_Classical_avram_p3_a_bvdrift_original_negative_jump_cutoff_antitone

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

/-- Original BV cutoff monotonicity converted into finite real totals. -/

theorem AvramDividend.Classical.avram_p3_a_bvdrift_original_finite_real_cutoff_antitone
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation) :
    ∀ᵐ ω ∂P, ∀ (T : ℝ≥0) (ε₁ ε₂ : ℝ≥0∞), ε₁ ≤ ε₂ →
      (∑' (u : ℝ≥0),
        if 0 < u ∧ u ≤ T ∧ ε₂ <
            ENNReal.ofReal
              (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        then ENNReal.ofReal
          (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0).toReal ≤
      (∑' (u : ℝ≥0),
        if 0 < u ∧ u ≤ T ∧ ε₁ <
            ENNReal.ofReal
              (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        then ENNReal.ofReal
          (Function.leftLim (fun z : ℝ≥0 => X.X z ω) u - X.X u ω)
        else 0).toReal := by sorry
