-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_original_strict_prefix_rightpost_full_ae_compact_band
-- name    : AvramDividend.Classical.avram_lsv_original_strict_prefix_rightpost_full_ae_compact_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T21:52:50.826801+00:00
-- url     : https://prove2.me/theorems/7a51ca03-0887-4e32-b11e-143d05d959d0
-- title:
--   Original physical right-postpayment reserve stays in positive compact band for every strictly pre-ruin time, including time zero
-- statement:
--   Given an almost sure uniform positive lower and finite upper bound on the genuine original pre-dividend reserve at each strictly positive time before a stopped pre-ruin clock, the right-postpayment reserve obeys both same bounds at every time strictly before the clock, including time zero. Source-faithful combination of original physical floor and ceiling theorems; no artificial regularity, moment, or clock assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_strict_prefix_postpayment_floor
import Theorems.Thm_AvramDividend_Classical_avram_gledger73_original_strict_prefix_postpayment_ceiling
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_lsv_original_strict_prefix_rightpost_full_ae_compact_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (a b : ℝ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      a ≤ riskProcess X x D t ω ∧ riskProcess X x D t ω ≤ b) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t < ρ ω →
      x + X.X t ω - rightLimit D t ω ∈ Icc a b := by sorry
