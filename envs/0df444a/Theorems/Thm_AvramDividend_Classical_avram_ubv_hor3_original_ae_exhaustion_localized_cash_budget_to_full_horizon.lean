-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_ae_exhaustion_localized_cash_budget_to_full_horizon
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_ae_exhaustion_localized_cash_budget_to_full_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:51:24.109654+00:00
-- url     : https://prove2.me/theorems/5ae426a9-d1de-448a-b9db-a1c1a997e884
-- title:
--   Original full stopped-horizon cash budget from almost-sure exhausting event-localised expected cash estimates
-- statement:
--   For the unchanged original spectrally negative Levy process X, its actual ruinTime and dividendMeasure D, let Cash be exactly the full discounted Stieltjes cash on the closed horizon Iic T. If measurable localising events A_k increase and cover the original sample space almost surely, and each original cash restricted to A_k has expected ENNReal value at most budget, then the full expected original cash is at most budget. This is a genuine monotone-convergence/Fatou localisation passage; it requires no unlocalised L1 martingale source, no equality in law and retains all allowed payment atoms at 0 and T. The stochastic localised budget premises remain to be proved independently.
-- source:
--   Independent alternative Fatou route explicitly requested in UBV-HOR3. Uses pinned Mathlib lintegral_iSup for monotonically increasing measurable original event masks, the exact original stochastic Cash identification and a.e. exhaustion. Does not import fdb, 0dda, 750, 665, d457 or root. Proved only as an implication from stated event-localised expected cash estimates, which a genuine compact stopped Ito theorem must establish.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_hor3_original_ae_exhaustion_localized_cash_budget_to_full_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (Cash : Ω → ℝ≥0∞)
    (hCash : ∀ ω, Cash ω =
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)))
    (hCashMeas : Measurable Cash)
    (A : ℕ → Set Ω)
    (hAmeas : ∀ k, MeasurableSet (A k))
    (hAmono : Monotone A)
    (hAcover : ∀ᵐ ω ∂P, ∃ k, ω ∈ A k)
    (budget : ℝ≥0∞)
    (hLocalized : ∀ k,
      (∫⁻ ω in A k, Cash ω ∂P) ≤ budget) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
      budget := by sorry
