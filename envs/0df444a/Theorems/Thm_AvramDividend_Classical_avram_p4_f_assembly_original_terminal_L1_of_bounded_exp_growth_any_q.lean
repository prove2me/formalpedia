-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_terminal_L1_of_bounded_exp_growth_any_q
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_terminal_L1_of_bounded_exp_growth_any_q
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:15:38.250348+00:00
-- url     : https://prove2.me/theorems/29054c1d-9399-4a5d-9687-14565529d1a9
-- title:
--   Original stopped terminal L1 from exponential candidate growth for arbitrary discount q
-- statement:
--   For the true original stopped postpayment-or-ruin reserve W and terminal Term at a bounded right-continuous clock, prove L1 given a valid candidate exponential envelope, for any q without ψθ≤q. The source Esscher correction is bounded at a finite horizon, and the all-source terminal envelope transfers integrability. Only the candidate-growth hypothesis remains additional.
-- source:
--   Original source unrestricted-q discounted exponential L1 helper and Proved exact terminal raw envelope c25fc0e9. Source imported unrestricted-q original discounted exponential moment b91875a4-9d48-4c3c-b658-ef43e2d93862 is now independently Proved.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_bounded_stop_discounted_exp_integrable_any_q
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_terminal_L1_of_integrable_source_exponential_envelope
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_terminal_L1_of_bounded_exp_growth_any_q
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
    Integrable Term P := by sorry
