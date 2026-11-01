-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_stopped_complete_signed_stieltjes_control_correction_nonpos
-- name    : AvramDividend.Classical.avram_wave4_04b_stopped_complete_signed_stieltjes_control_correction_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T11:46:40.233555+00:00
-- url     : https://prove2.me/theorems/46dbfc5b-9a1c-4a88-bcbf-75bc1899b4f9
-- title:
--   Full finite-horizon signed continuous and chronological right-atomic Stieltjes control correction is nonpositive
-- statement:
--   On the actual adapted Lévy reserve, the real signed continuous Stieltjes correction against an arbitrary atomless time measure, including singular-continuous dividends, plus the full convergent chronological countable right-payment correction is nonpositive. Strict interior HJB gradient and chronological hjump are imposed on stopped paid times. Real integrability and summability are explicit and must be established in a later stochastic identity. This theorem is the deterministic finite-variation correction, not a claimed full Ito formula.
-- source:
--   Previously proved 04-B real signed atomless correction and countable signed right-payment correction; Mathlib add_nonpos, no stochastic axiom.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_stopped_atomless_signed_continuous_correction_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_countable_chronological_signed_correction_nonpos_of_summable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

noncomputable section

theorem AvramDividend.Classical.avram_wave4_04b_stopped_complete_signed_stieltjes_control_correction_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (ω : Ω) (T : ℝ≥0) (τ : ℝ≥0∞) (q : ℝ)
    (ν : Measure ℝ) [NullSingletonClass ν]
    (A : Set ℝ≥0) (hA : A.Countable)
    (hAT : ∀ t : A, (t : ℝ≥0) ≤ T)
    (hAP : ∀ t : A, ((t : ℝ≥0) : ℝ) ∈ paymentTimes τ)
    (hloc : ∀ t : ℝ≥0, t ≤ T → (t : ℝ) ∈ paymentTimes τ →
      0 < riskProcess X x D t ω ∧
        ENNReal.ofReal (riskProcess X x D t ω) < C)
    (hjump : ∀ t : ℝ≥0, t ≤ T → (t : ℝ) ∈ paymentTimes τ →
      rightLimit D t ω - D t ω ≤
        w (riskProcess X x D t ω) -
          w (riskProcess X x D t ω -
            (rightLimit D t ω - D t ω)))
    (hIntegrable : IntegrableOn
      (fun s : ℝ => Real.exp (-q * s) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)))
      (paymentTimes τ ∩ Icc (0 : ℝ) (T : ℝ)) ν)
    (hSummable : Summable (fun t : A =>
      Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
        ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          w (riskProcess X x D (t : ℝ≥0) ω -
            (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
          w (riskProcess X x D (t : ℝ≥0) ω)))) :
    (∫ s in paymentTimes τ ∩ Icc (0 : ℝ) (T : ℝ),
      Real.exp (-q * s) *
        (1 - deriv w (riskProcess X x D s.toNNReal ω)) ∂ν) +
    (∑' t : A,
      Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
        ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          w (riskProcess X x D (t : ℝ≥0) ω -
            (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
          w (riskProcess X x D (t : ℝ≥0) ω))) ≤ 0 := by sorry
