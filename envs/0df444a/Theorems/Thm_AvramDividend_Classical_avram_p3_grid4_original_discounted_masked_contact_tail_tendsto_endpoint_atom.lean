-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_discounted_masked_contact_tail_tendsto_endpoint_atom
-- name    : AvramDividend.Classical.avram_p3_grid4_original_discounted_masked_contact_tail_tendsto_endpoint_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:04:28.508206+00:00
-- url     : https://prove2.me/theorems/3240dd0b-ce06-468d-b56f-668cf0bac931
-- title:
--   Actual original finite discounted contact cash converges to the exact payment-masked endpoint atom
-- statement:
--   Using the actual original dividendMeasure D omega and paymentTimes(ruinTime X x D omega), a monotone positive real width sequence delta_n→0 yields convergence of weighted half-open stopped cash tails to precisely the surviving weighted endpoint singleton. Finiteness follows from the Proved original closed-horizon discounted Stieltjes budget. Continuity from above preserves the potential right-payment atom at survivor T and excludes the positive ruin atom via paymentTimes. No abstract replacement process, zero-atom assumption or global uniform L1 bound is introduced.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_literal_stopped_payment_cash_lintegral_finite
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_discounted_masked_contact_tail_tendsto_endpoint_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q : ℝ) (hq : 0 ≤ q)
    (T τ : ℝ≥0) (hτT : τ ≤ T)
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδanti : Antitone δ)
    (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc ((τ : ℝ) - δ n) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop
      (𝓝 (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        ({(τ : ℝ)} : Set ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) := by sorry
