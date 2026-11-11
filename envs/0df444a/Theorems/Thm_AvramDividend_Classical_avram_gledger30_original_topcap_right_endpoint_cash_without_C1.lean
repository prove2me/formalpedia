-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger30_original_topcap_right_endpoint_cash_without_C1
-- name    : AvramDividend.Classical.avram_gledger30_original_topcap_right_endpoint_cash_without_C1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T18:04:56.624272+00:00
-- url     : https://prove2.me/theorems/d27ba81b-e818-461e-96af-d176166fc1a6
-- title:
--   Original right-endpoint dividend cash cell bound from derivative-only secants
-- statement:
--   For an actual dividend strategy and a deterministic interval, suppose the original postpayment endpoint capital is nonnegative and the original right-dividend increment is nonnegative. A reward continuous on nonnegative reserves whose positive derivative is at least one gives a discounted Stieltjes upper bound by the original endpoint reward drop plus the mesh discount error. This removes the unnecessarily strong C1 hypothesis from the existing upper-cell result, and is intended for the full cells before the physical Gaussian stopped clock in Gaussian27.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger30_original_topcap_right_endpoint_cash_without_C1
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (a b : ℝ≥0) (hab : a ≤ b)
    (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_grad : ∀ y : ℝ, 0 < y → 1 ≤ deriv w y)
    (A : ℝ) (hpost : 0 ≤ A - rightLimit D b ω)
    (hinc : 0 ≤ rightLimit D b ω - rightLimit D a ω) :
    (∫⁻ s in Ioc (a : ℝ) (b : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * (b : ℝ)))) *
        ENNReal.ofReal (w (A - rightLimit D a ω) - w (A - rightLimit D b ω)) +
      ENNReal.ofReal (q * ((b : ℝ) - (a : ℝ))) *
        dividendMeasure D ω (Ioc (a : ℝ) (b : ℝ)) := by sorry
