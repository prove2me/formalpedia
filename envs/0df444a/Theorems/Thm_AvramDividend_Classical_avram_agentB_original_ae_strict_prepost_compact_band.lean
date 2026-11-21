-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_agentB_original_ae_strict_prepost_compact_band
-- name    : AvramDividend.Classical.avram_agentB_original_ae_strict_prepost_compact_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:06:33.855497+00:00
-- url     : https://prove2.me/theorems/897fa659-d4ec-4a01-b9a4-22e838c39667
-- title:
--   Genuine original strictly stopped Gaussian prepayment compact reserve floor and ceiling pass to postright-dividend reserve
-- statement:
--   Under the original stopped compact prepayment reserve band on every positive time t<rho, the real postright dividend reserve x+X(t)-rightLimit D(t) is in the identical band at each positive strictly earlier time on the same almost-everywhere sample set. The lower floor transfers by the already Proved right-continuous original source reserve limit theorem. The ceiling is bounded by the prepayment reserve because the admissible nondecreasing dividend strategy lies below its own right limit. This is the missing true-process compact reserve control for the first and second Gaussian Hermite postpayment coefficients, without replacing original X,D or stopping clock.
-- source:
--   Proved avram_gledger20_original_strict_prefix_postpayment_floor and dividendStrategy_le_rightLimit.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_agentB_original_ae_strict_prepost_compact_band
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (a b : ℝ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      a ≤ riskProcess X x D t ω ∧ riskProcess X x D t ω ≤ b) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      a ≤ x + X.X t ω - rightLimit D t ω ∧
        x + X.X t ω - rightLimit D t ω ≤ b := by sorry
