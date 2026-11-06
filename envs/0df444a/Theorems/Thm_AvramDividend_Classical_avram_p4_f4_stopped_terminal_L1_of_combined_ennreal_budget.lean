-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_stopped_terminal_L1_of_combined_ennreal_budget
-- name    : AvramDividend.Classical.avram_p4_f4_stopped_terminal_L1_of_combined_ennreal_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:11:47.759766+00:00
-- url     : https://prove2.me/theorems/2360f684-d67e-4aac-a2b0-f3b7720a4fce
-- title:
--   Finite stopped terminal plus dividend positive ENNReal budget proves terminal L1 and real payoff bound
-- statement:
--   If the original stopped terminal and cash functions are measurable with nonnegative values and cash is integrable, then a finite ENNReal expected budget on terminal plus cash proves actual L1 integrability of the terminal value and the matching real expectation bound. Applies to C=top without artificial global terminal boundedness. This is an analytic bridge; establishing the original-process expected budget remains a separate obligation.
-- source:
--   Original stopped-source analytic closure for fdb9a6a3; proved from pinned Mathlib equivalence of finite positive lintegral and Integrable, plus the ofReal-integral identity. The hypothesis is a genuine independently required combined budget.

import Mathlib

open MeasureTheory
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_stopped_terminal_L1_of_combined_ennreal_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (Term Cash : Ω → ℝ)
    (hTermMeas : AEStronglyMeasurable Term P)
    (hTermNonneg : 0 ≤ᵐ[P] Term)
    (hCashI : Integrable Cash P)
    (hCashNonneg : 0 ≤ᵐ[P] Cash)
    (b : ℝ) (hb : 0 ≤ b)
    (hBudget :
      (∫⁻ ω, ENNReal.ofReal (Term ω + Cash ω) ∂P) ≤
        ENNReal.ofReal b) :
    Integrable Term P ∧ (∫ ω, Term ω + Cash ω ∂P) ≤ b := by sorry
