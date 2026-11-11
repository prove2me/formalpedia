-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger73_original_strict_prefix_postpayment_ceiling
-- name    : AvramDividend.Classical.avram_gledger73_original_strict_prefix_postpayment_ceiling
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T01:45:07.797364+00:00
-- url     : https://prove2.me/theorems/d651b180-45a4-44a3-a4e7-c8a6b954af91
-- title:
--   Original strict prepayment compact ceiling extends through every postpayment right limit
-- statement:
--   For the original spectrally negative Lévy process and genuine dividend strategy, any deterministic upper prepayment reserve ceiling on every strictly positive time before a stopped horizon transfers to the actual postpayment reserve, including at time zero. This is the necessary upper half of the original compact-band source envelope for gledger72.
-- source:
--   Root-connected gledger72 physical active-cell compact envelope. Direct source-exact upper analogue of proved gledger20; no process replacement.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger73_original_strict_prefix_postpayment_ceiling
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (ρ : ℝ≥0) (b : ℝ)
    (hprefix : ∀ t : ℝ≥0, 0 < t → t < ρ →
      riskProcess X x D t ω ≤ b) :
    ∀ t : ℝ≥0, t < ρ →
      x + X.X t ω - rightLimit D t ω ≤ b := by sorry
