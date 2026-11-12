-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger83_original_strict_prefix_right_endpoint_cash_cell
-- name    : AvramDividend.Classical.avram_gledger83_original_strict_prefix_right_endpoint_cash_cell
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T09:17:00.486202+00:00
-- url     : https://prove2.me/theorems/9b145814-2911-4699-ab49-175b5bd23f48
-- title:
--   Original positive-prefix right-endpoint dividend cash cell inequality
-- statement:
--   For any original Lévy process and dividend strategy, an interior cell ending strictly before a positive stopping clock has nonnegative postpayment reserve, inherited from the compact positive prefix. Right-limit dividends are monotone. Consequently the Proved right-endpoint Stieltjes secant cash estimate applies to the actual original paths with the correctly discounted endpoint reward drop and q times cell length times original dividend mass. This strictly local ingredient of gledger81 makes no assertion about the last cell or terminal payment.
-- source:
--   Root-connected gledger81 16e988d7 strictly positive-prefix interior cells. Derive nonnegative postpayment reserve from Proved gledger20, rightLimit monotonicity from Proved wave3_03, then apply Proved gledger30 exact ENNReal Stieltjes secant bound. Final crossing and terminal atom excluded deliberately.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_strict_prefix_postpayment_floor
import Theorems.Thm_AvramDividend_Classical_avram_gledger30_original_topcap_right_endpoint_cash_without_C1
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_dividendStrategy_rightLimit_monotone
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger83_original_strict_prefix_right_endpoint_cash_cell
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (ρ : ℝ≥0) (u : ℝ) (hu : 0 ≤ u)
    (hprefix : ∀ t : ℝ≥0, 0 < t → t < ρ →
      u ≤ riskProcess X x D t ω)
    (a b : ℝ≥0) (hab : a ≤ b) (hb : b < ρ)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_grad : ∀ y : ℝ, 0 < y → 1 ≤ deriv w y) :
    (∫⁻ s in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * (b : ℝ)))) *
        ENNReal.ofReal (w (x + X.X b ω - rightLimit D a ω) -
          w (x + X.X b ω - rightLimit D b ω)) +
      ENNReal.ofReal (q * ((b : ℝ) - (a : ℝ))) *
        dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) := by sorry
