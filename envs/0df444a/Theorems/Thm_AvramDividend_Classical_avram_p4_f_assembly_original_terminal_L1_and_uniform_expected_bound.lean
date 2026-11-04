-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_terminal_L1_and_uniform_expected_bound
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_terminal_L1_and_uniform_expected_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:46:16.321282+00:00
-- url     : https://prove2.me/theorems/3b3bed9d-8df6-48ca-888f-51c0e2793c6a
-- title:
--   True stopped terminal L1 and explicit uniform expected payoff bound at every bounded source clock
-- statement:
--   For the exact original source and postpayment-or-ruin stopped terminal, deduce integrability and E Term≤K e^(θx) e^(|ψθ−q|H), assuming an explicit candidate exponential growth envelope and nonnegative original terminal. The estimate is quantitative, valid for every q and finite H, and directly uses the genuine stopped Esscher moment bound, without replacing the process or asserting the canonical HJB implies candidate growth.
-- source:
--   Accepted unrestricted-q source exponential L1 b91875a4, accepted source uniform moment bound 7bd787b2, and accepted source terminal envelope ed63338c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_bounded_stop_discounted_exp_integrable_any_q
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_bounded_stop_discounted_exp_mean_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_terminal_from_source_exponential_growth_envelope
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_terminal_L1_and_uniform_expected_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (w : ℝ → ℝ) (q θ K : ℝ)
    (hθ : 0 ≤ θ) (hK : 0 ≤ K)
    (hwGrowth : ∀ y : ℝ, w y ≤ K * Real.exp (θ * y))
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hTermNonneg : ∀ᵐ ω ∂P, 0 ≤ Term ω) :
    Integrable Term P ∧
      (∫ ω, Term ω ∂P) ≤
        (K * Real.exp (θ * x)) *
          Real.exp (|X.ψ θ - q| * (H : ℝ)) := by sorry
