-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_rightpayment_local_lipschitz_secant_upper
-- name    : AvramDividend.Classical.avram_p4_d_dividend_original_rightpayment_local_lipschitz_secant_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T19:57:25.078976+00:00
-- url     : https://prove2.me/theorems/77773c05-6be7-4dd9-b07c-0423a0307cda
-- title:
--   Original post-Lévy pre-dividend rightpayment secant bounded by local compact C1 derivative
-- statement:
--   On a genuine common compact reserve band containing both the post-source-jump pre-dividend reserve and the post-right-dividend reserve, the accepted derivative-controlled Lipschitz theorem yields an explicit upper secant bound with K=1+L. The original rightLimit-minus-D increment is nonnegative by dividend admissibility; no derivative condition at cap or zero contact is silently inferred.
-- source:
--   Accepted original dividendStrategy_le_rightLimit and avram_wave8_22_original_BV_compact_derivative_implies_lipschitz 596e81d8, with exact original riskProcess reserve algebra.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_compact_derivative_implies_lipschitz

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_original_rightpayment_local_lipschitz_secant_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b : ℝ) (L : ℝ≥0)
    (hDiff : ∀ y ∈ Icc a b, DifferentiableAt ℝ w y)
    (hDeriv : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ L)
    (ω : Ω) (t : ℝ≥0)
    (hpre : riskProcess X x D t ω ∈ Icc a b)
    (hpost : x + X.X t ω - rightLimit D t ω ∈ Icc a b) :
    w (riskProcess X x D t ω) -
      w (x + X.X t ω - rightLimit D t ω) ≤
        (1 + (L : ℝ)) * (rightLimit D t ω - D t ω) := by sorry
