-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f4_ae_natural_clock_fatou_L1_budget
-- name    : AvramDividend.Classical.avram_p4_f4_ae_natural_clock_fatou_L1_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:49:16.415539+00:00
-- url     : https://prove2.me/theorems/a400dff7-b5be-40c5-aa47-13d192b40fad
-- title:
--   Almost-sure cofinal original stochastic localisers yield natural-clock real L1 Fatou budget
-- statement:
--   Real-valued nonnegative physical local reward approximants F_k whose ENNReal.ofReal values converge to the full stopped reward almost surely satisfy the same real expectation budget and full reward L1 integrability. This strengthens the existing pointwise-convergence F4 Fatou theorem by allowing the exceptional null set intrinsic to stochastic cofinal localisers, without any uniform-integrability assumption or unproved convergence hypothesis.
-- source:
--   Direct pinned-Mathlib Fatou lintegral_liminf_le and Filter.Tendsto.liminf_eq, valid a.e. under actual probability measure. Applied next to source original stopped cofinal sequence; local Ito expectation inequality remains independent.

import Mathlib

open MeasureTheory Filter Topology
open scoped ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p4_f4_ae_natural_clock_fatou_L1_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (S : Ω → ℝ) (F : ℕ → Ω → ℝ)
    (hSmeas : AEStronglyMeasurable S P)
    (hSnonneg : 0 ≤ᵐ[P] S)
    (hFmeas : ∀ k, Measurable (F k))
    (hFint : ∀ k, Integrable (F k) P)
    (hFnonneg : ∀ k, 0 ≤ᵐ[P] F k)
    (hlim : ∀ᵐ ω ∂P, Tendsto
      (fun k => ENNReal.ofReal (F k ω)) atTop
      (𝓝 (ENNReal.ofReal (S ω))))
    (b : ℝ) (hb : 0 ≤ b)
    (hBudget : ∀ k, (∫ ω, F k ω ∂P) ≤ b) :
    Integrable S P ∧ (∫ ω, S ω ∂P) ≤ b := by sorry
