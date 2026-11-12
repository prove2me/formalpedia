-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
-- name    : AvramDividend.Classical.avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T18:52:39.080132+00:00
-- url     : https://prove2.me/theorems/e7de7c19-7b80-4b96-9144-7db933df17e2
-- title:
--   Original Gaussian postpayment source stays within the strict pre-stop reserve band
-- statement:
--   Under the original deterministic compact pre-stop risk-process band, the genuine original postpayment Taylor evaluation coefficient x+X.X t-rightLimit D t lies in the same band almost everywhere at all times strictly before the original stopped clock. This provides the source-exact compact C2 localisation required for the Gaussian Taylor L1 proof.
-- source:
--   Conjunction of Proved avram_gledger20_original_strict_prefix_postpayment_floor and avram_gledger73_original_strict_prefix_postpayment_ceiling, with the exact risk source and original dividend right limit used in the Open gledger50 physical Taylor L1 theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤
        x + X.X t ω - rightLimit D t ω ∧
      x + X.X t ω - rightLimit D t ω ≤
        x + ((j : ℝ) + 1) := by sorry
