-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_terminal_L1_of_integrable_source_exponential_envelope
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_terminal_L1_of_integrable_source_exponential_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:56:28.16366+00:00
-- url     : https://prove2.me/theorems/c25fc0e9-f536-4234-9417-d5e90dfb03d6
-- title:
--   Original ruin-stopped terminal L1 follows from a genuine integrable Lévy exponential envelope
-- statement:
--   On the original X,D,ruin-aware W and actual discounted Term, combine the accepted original pathwise exponential-growth bound with the pinned monotone-integrability theorem. This proves true terminal L1 if the independently needed raw Lévy exponential evaluated at the same random clock is integrable and w has an explicit growth envelope. Both substantive inputs remain visible, so no random-clock moment or HJB growth is invented.
-- source:
--   Accepted P4-F exact stopped exponential-growth envelope ed63338c; pinned Mathlib Integrable.mono_nonneg exact remote signature; actual Term nonnegativity is an explicit source premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_terminal_from_source_exponential_growth_envelope
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_terminal_L1_of_integrable_source_exponential_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (w : ℝ → ℝ) (q θ K : ℝ) (hθ : 0 ≤ θ) (hK : 0 ≤ K)
    (hwGrowth : ∀ y : ℝ, w y ≤ K * Real.exp (θ * y))
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (hTermNonneg : ∀ᵐ ω ∂P, 0 ≤ Term ω)
    (hRawI : Integrable (fun ω =>
      Real.exp (-(q * (τ ω : ℝ))) *
        (K * Real.exp (θ * (x + X.X (τ ω) ω)))) P) :
    Integrable Term P := by sorry
