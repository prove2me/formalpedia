-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f13_original_natural_clock_constant_family_integrable_source
-- name    : AvramDividend.Classical.avram_p4_f13_original_natural_clock_constant_family_integrable_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:50:49.063891+00:00
-- url     : https://prove2.me/theorems/4842d5fa-a962-4171-a53f-96639bf829ce
-- title:
--   True original natural stopped clock gives an integrable exact constant payoff family
-- statement:
--   Given the original stopped reserve W, discounted terminal Term, inclusive Stieltjes Cash and their genuine L1 integrability, construct the constant clock family σₖ=τ and exact stopped rewards Fₖ=Term+Cash. Prove all clock stopping times, bounds, original payoff identities, integrability and equality of the natural and family integrals.
-- source:
--   Independent source-exact witness construction, usable by both mixed Gaussian and purejump finite-cap verification reductions; no derivative, HJB, martingale, or policy change hypotheses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f13_original_natural_clock_constant_family_integrable_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (W Cash Term : Ω → ℝ)
    (hW : ∀ ω, W ω = if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hCash : ∀ ω, Cash ω = (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
      ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal)
    (hTerm : ∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermI : Integrable Term P) (hCashI : Integrable Cash P) :
    ∃ (σ : ℕ → Ω → ℝ≥0) (F : ℕ → Ω → ℝ),
      (∀ k, IsStoppingTime 𝓕.rightCont (fun ω => (σ k ω : WithTop ℝ≥0))) ∧
      (∀ k ω, σ k ω ≤ τ ω) ∧
      (∀ k ω, F k ω =
        Real.exp (-(q * (σ k ω : ℝ))) *
          w (if σ k ω = 0 ∨ (σ k ω : ℝ≥0∞) < ruinTime X x D ω then
            x + X.X (σ k ω) ω - rightLimit D (σ k ω) ω
          else riskProcess X x D (σ k ω) ω) +
        (∫⁻ s in paymentTimes (ruinTime X x D ω) ∩ Iic (σ k ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s))) ∂(dividendMeasure D ω)).toReal) ∧
      (∀ k, Integrable (F k) P) ∧
      (∫ ω, F 0 ω ∂P) = (∫ ω, Term ω + Cash ω ∂P) := by sorry
