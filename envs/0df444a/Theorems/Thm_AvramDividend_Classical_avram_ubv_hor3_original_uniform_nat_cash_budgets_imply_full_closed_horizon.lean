-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_uniform_nat_cash_budgets_imply_full_closed_horizon
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_uniform_nat_cash_budgets_imply_full_closed_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:37:29.036805+00:00
-- url     : https://prove2.me/theorems/196220b2-3dca-467f-8bb3-543957311b63
-- title:
--   Uniform true stopped cash budgets imply the exact untruncated original ruin cash on every closed finite horizon
-- statement:
--   For the unchanged original Levy X and dividendMeasure D, if the genuine discounted dividend cash on the closed horizon Iic T is bounded uniformly over all positive natural clipping times n, then the original untruncated ruin-time discounted dividend cash on the very same closed horizon has the identical upper bound. Choose n strictly exceeding max(T,0) via Archimedean existence and invoke the previously Proved exact cash identity for T<n. No limit passage, loss of time-zero or horizon atoms, or synthetic process is involved. This is a source-exact conditional implication that can consume the canonical positive-natural bounded-clock theorem once Proved.
-- source:
--   Original cash-horizon limit bridge independent of Open canonical targets. Imports only Proved public 4569b16d cash equality and exact pinned Mathlib exists_nat_gt. The family of original stopped budgets is an explicit hypothesis and remains the canonical stochastic task; the reduction itself is genuine and complete.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_clock_beyond_closed_horizon_cash_eq_unclipped_ruin
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_hor3_original_uniform_nat_cash_budgets_imply_full_closed_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x q T : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (budget : ℝ≥0∞)
    (hEach : ∀ (n : ℕ), 0 < n →
      (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ budget) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤ budget := by sorry
