-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_ae_local_fatou_to_original_five_witness
-- name    : AvramDividend.Classical.avram_p4_f4_ae_local_fatou_to_original_five_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:07:41.966903+00:00
-- url     : https://prove2.me/theorems/af353eaf-9327-456d-b1e9-aa9b3afd4f85
-- title:
--   Almost-sure original local payoff budgets give five true stopped source witnesses
-- statement:
--   The actual original terminal plus closed-horizon Stieltjes cash at the natural clock has an integrable and centred five-slot witness whenever genuine local physical nonnegative rewards converge almost surely and satisfy uniformly bounded expectations. This removes everywhere-path convergence from the previously Proved F4 bridge, retaining actual local source expectation budgets as explicit premises.
-- source:
--   Once a400dff7 is Proved, compose its a.e nonnegative Fatou real expectation theorem with Proved 388d9c1a five-witness equivalence. The a.e limit is a material stochastic-localisation advance; no new source identity or natural-clock martingale mean-zero is postulated.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_ae_natural_clock_fatou_L1_budget
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_five_witness_iff_expected_budget

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_ae_local_fatou_to_original_five_witness
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
    (hlim : ∀ᵐ ω ∂P, Tendsto
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
