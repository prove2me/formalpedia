-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_nonnegative_natural_clock_fatou_L1_budget
-- name    : AvramDividend.Classical.avram_p4_f4_nonnegative_natural_clock_fatou_L1_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:02:13.856563+00:00
-- url     : https://prove2.me/theorems/e4077f6a-2350-488f-a693-7ed9d0240899
-- title:
--   Natural-clock nonnegative Fatou payoff budgets give L1 integrability and real expectation bound
-- statement:
--   For the nonnegative true stopped terminal-plus-dividend payoff S, any measurable integrable nonnegative physical localised rewards F_k whose ENNReal.ofReal values converge pointwise to S and whose expectations are uniformly bounded by nonnegative b yield both integrability of S and E[S] ≤ b. This obtains natural-clock L1 from the local budgets rather than assuming uniform integrability of the individual Gaussian and jump martingales. The original stopped physical payoff convergence and finite-localiser budgets remain separate obligations.
-- source:
--   Analytic natural-clock closure sublemma for fdb9a6a3. Reuse the Proved one_sided_lintegral_le_of_grid_tendsto plus exact pinned Mathlib integrability iff finite lintegral and ofReal integral identity; it proves L1 and the real budget without assuming L1 convergence of the centred martingales. It does not assert a stochastic original-X identity or discharge the pointwise convergence/budget premises.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_one_sided_lintegral_le_of_grid_tendsto

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_nonnegative_natural_clock_fatou_L1_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Ω → ℝ) (F : ℕ → Ω → ℝ)
    (hSmeas : AEStronglyMeasurable S P)
    (hSnonneg : 0 ≤ᵐ[P] S)
    (hFmeas : ∀ k, Measurable (F k))
    (hFint : ∀ k, Integrable (F k) P)
    (hFnonneg : ∀ k, 0 ≤ᵐ[P] F k)
    (hlim : ∀ ω, Tendsto
      (fun k => ENNReal.ofReal (F k ω)) atTop
      (𝓝 (ENNReal.ofReal (S ω))))
    (b : ℝ) (hb : 0 ≤ b)
    (hBudget : ∀ k, (∫ ω, F k ω ∂P) ≤ b) :
    Integrable S P ∧ (∫ ω, S ω ∂P) ≤ b := by sorry
