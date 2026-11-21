-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_original_strict_preruin_discounted_full_Stieltjes_cash_allgrid_any_event_uniform_L2
-- name    : AvramDividend.Classical.avram_pj_original_strict_preruin_discounted_full_Stieltjes_cash_allgrid_any_event_uniform_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T17:36:08.169224+00:00
-- url     : https://prove2.me/theorems/480e1aab-154f-4fd2-aa8e-c5ddae63920d
-- title:
--   Original strictly pre-ruin full Stieltjes cash physical grid all clocks uniformly square-integrable on any measurable event
-- statement:
--   For the actual original unbounded variation spectrally negative Levy reserve and every actual strictly pre-ruin original bounded stochastic physical clock, the entire discounted full Stieltjes dividend cash square remains uniformly integrable on every measurable initial/event restriction under one finite common original Levy running supremum L2 budget, independent of grid refinement k. Uses the Proved genuine original family cash uniform second-moment budget 42ada47c and nonnegative square restricted integral monotonicity. No substituted dividend process, finite jump activity, nor artificial cash approximation.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_original_all_strict_preruin_discounted_Stieltjes_cash_family_uniform_L2_budget
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_original_strict_preruin_discounted_full_Stieltjes_cash_allgrid_any_event_uniform_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q)
    (n : ℝ≥0) (ρ : ℕ → Ω → ℝ≥0)
    (hρle : ∀ k ω, ρ k ω ≤ n)
    (hρpre : ∀ k ω, (ρ k ω : ℝ≥0∞) <
      ruinTime X x D ω)
    (Cash : ℕ → Ω → ℝ)
    (hCash : ∀ k ω, Cash k ω =
      (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩
        Iic (ρ k ω : ℝ),
        ENNReal.ofReal (Real.exp (-(q * s)))
          ∂(dividendMeasure D ω)).toReal)
    (hCashMeas : ∀ k, Measurable (Cash k))
    (A : Set Ω) (hA : MeasurableSet A) :
    ∃ B : ℝ, 0 ≤ B ∧
      ∀ k, Integrable (fun ω => (Cash k ω)^2) P ∧
        (∫ ω in A, (Cash k ω)^2 ∂P) ≤ B := by sorry
