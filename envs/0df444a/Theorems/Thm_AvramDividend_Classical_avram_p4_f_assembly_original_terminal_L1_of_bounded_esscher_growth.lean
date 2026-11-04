-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_terminal_L1_of_bounded_esscher_growth
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_terminal_L1_of_bounded_esscher_growth
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:23:39.27277+00:00
-- url     : https://prove2.me/theorems/c8e91b61-75c0-48fb-8c65-a097bcef1425
-- title:
--   Original stopped terminal integrability from a valid Esscher growth envelope at a bounded genuine clock
-- statement:
--   Under a verified candidate growth bound w(y)≤K exp(θy), actual original terminal W/Term definitions, a genuinely bounded right-continuous stopping time, real clock measurability and ψθ≤q, the original terminal is L1. Derive its source raw exponential integrability using the new original-process stopped Esscher theorem, then reuse the separately Proved original upper domination and L1 transfer. No independent source process or extra cash assumptions.
-- source:
--   Proved original terminal envelope L1 transfer c25fc0e9 and new P4-F source stopped exponential L1 helper 00c43baf (proof pending). Conditional candidate-growth hypothesis remains explicit, not claimed from canonical.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_rightCont_bounded_stop_discounted_exp_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_terminal_L1_of_integrable_source_exponential_envelope
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_terminal_L1_of_bounded_esscher_growth
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
    (hθ : 0 ≤ θ) (hq : X.ψ θ ≤ q) (hK : 0 ≤ K)
    (hwGrowth : ∀ y : ℝ, w y ≤ K * Real.exp (θ * y))
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hTermNonneg : ∀ᵐ ω ∂P, 0 ≤ Term ω) :
    Integrable Term P := by sorry
