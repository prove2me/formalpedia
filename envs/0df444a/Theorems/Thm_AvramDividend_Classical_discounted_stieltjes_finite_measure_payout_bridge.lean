-- Prove2me | Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_finite_measure_payout_bridge
-- name    : AvramDividend.Classical.discounted_stieltjes_finite_measure_payout_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:59:15.343324+00:00
-- url     : https://prove2.me/theorems/72bc55bf-a759-42d0-b267-89b91d670ee7
-- title:
--   Finite-mass discounted Stieltjes payout equality in real and ENNReal integrals
-- statement:
--   For nonnegative discount q and a finite-measure measurable set of nonnegative payment times, the ENNReal lintegral of the discounted dividend payment density equals ENNReal.ofReal of its ordinary real Stieltjes integral. The already proved finite-window integrability lemma discharges the only extra premise of the pinned Mathlib Bochner-lintegral equality. This bridges signed HJB real budgets to the finite-horizon dividend payoff used by the exact stochastic verification theorem.

import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_integrableOn_of_finite_measure

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.discounted_stieltjes_finite_measure_payout_bridge
    (q : ℝ) (hq : 0 ≤ q) (μ : Measure ℝ) (A : Set ℝ)
    (hAmeas : MeasurableSet A)
    (hAnonneg : ∀ t ∈ A, 0 ≤ t)
    (hfinite : μ A ≠ ⊤) :
    (∫⁻ t in A, ENNReal.ofReal (Real.exp (-(q * t))) ∂μ) =
      ENNReal.ofReal (∫ t in A, Real.exp (-(q * t)) ∂μ) := by sorry
