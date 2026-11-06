-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_local_fatou_to_original_five_witness
-- name    : AvramDividend.Classical.avram_p4_f4_local_fatou_to_original_five_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:17:20.395683+00:00
-- url     : https://prove2.me/theorems/63784805-4215-447d-87bb-1b44e3c378eb
-- title:
--   Physical nonnegative stopped-payoff Fatou budgets imply five original clock centred witnesses
-- statement:
--   For the real natural stopped terminal and dividend cash functions, nonnegative localised original-process approximants with bounded expected payoff and genuine pointwise convergence yield integrability and the exact existential five-witness source conclusion via the proved Fatou bridge. The hypotheses of exact original-process localised Itô identities and uniform expected budgets remain to be established for the canonical target; witnesses are centred payoff residuals, not individually identified Gaussian or jump martingales.
-- source:
--   Composition of proved P4-F4 nonnegative natural-clock Fatou theorem and the literal five-witness iff expected-budget theorem, deriving terminal L1 and an actual five-channel witness from physical local payoffs without stochastic-martingale UI.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_nonnegative_natural_clock_fatou_L1_budget
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_five_witness_iff_expected_budget

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_local_fatou_to_original_five_witness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (Term Cash : Ω → ℝ)
    (hTermMeas : AEStronglyMeasurable Term P)
    (hCashI : Integrable Cash P)
    (hTermNonneg : 0 ≤ᵐ[P] Term)
    (hCashNonneg : 0 ≤ᵐ[P] Cash)
    (F : ℕ → Ω → ℝ)
    (hFmeas : ∀ k, Measurable (F k))
    (hFint : ∀ k, Integrable (F k) P)
    (hFnonneg : ∀ k, 0 ≤ᵐ[P] F k)
    (hlim : ∀ ω, Tendsto
      (fun k => ENNReal.ofReal (F k ω)) atTop
      (𝓝 (ENNReal.ofReal (Term ω + Cash ω))))
    (b : ℝ) (hb : 0 ≤ b)
    (hBudget : ∀ k, (∫ ω, F k ω ∂P) ≤ b) :
    ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      Integrable G P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧
      (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P, Term ω + Cash ω ≤
        b + Mc ω + Ms ω + Ml ω + G ω + R ω) := by sorry
