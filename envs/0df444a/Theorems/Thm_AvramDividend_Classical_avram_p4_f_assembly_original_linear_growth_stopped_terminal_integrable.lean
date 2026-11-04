-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_linear_growth_stopped_terminal_integrable
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_linear_growth_stopped_terminal_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:26:08.531863+00:00
-- url     : https://prove2.me/theorems/883b2a08-b51d-4b07-a72d-5b3084a3cb35
-- title:
--   Original stopped UBV terminal is L1 under explicit linear candidate growth and a valid source Esscher exponent
-- statement:
--   For the exact original Lévy process, admissible capped dividend control, postpayment-or-ruin terminal and genuine right-continuous stopping time, prove terminal L1 from an explicit linear upper bound on the candidate and an Esscher exponent θ with ψ(θ)≤q. Its nonnegativity follows from the accepted original UBV all-branch lemma. This supplies a sufficient condition including infinite C, without pretending that canonical hypotheses imply global linear growth.
-- source:
--   Accepted original terminal sign f6fef241, new P4-F bounded stopped source exponential L1 00c43baf and source terminal-growth bridge c25fc0e9; direct linear growth envelope helper. Source linear exponential-envelope theorem 0f4733e0-a902-4995-bc9c-8cdb048b1030 now Proved; source import dependency is verified.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_linear_upper_growth_implies_exponential_envelope
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_terminal_L1_of_bounded_esscher_growth
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_linear_growth_stopped_terminal_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (x : ℝ) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (τ : Ω → ℝ≥0) (W Term : Ω → ℝ)
    (hτmeas : Measurable (fun ω => (τ ω : ℝ)))
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (H : ℝ≥0) (hbound : ∀ ω, τ ω ≤ H)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω)
    (hTerm : ∀ ω, Term ω =
      Real.exp (-(q * (τ ω : ℝ))) * w (W ω))
    (hTermMeas : AEStronglyMeasurable Term P)
    (θ B L K : ℝ) (hθ : 0 ≤ θ) (hψ : X.ψ θ ≤ q)
    (hK : 0 ≤ K) (hB : B ≤ K) (hL : L ≤ K * θ)
    (hlinear : ∀ y : ℝ, 0 ≤ y → w y ≤ B + L * y) :
    Integrable Term P := by sorry
