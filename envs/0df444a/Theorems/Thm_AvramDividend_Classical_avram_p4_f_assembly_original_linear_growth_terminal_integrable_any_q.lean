-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_linear_growth_terminal_integrable_any_q
-- name    : AvramDividend.Classical.avram_p4_f_assembly_original_linear_growth_terminal_integrable_any_q
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:29:41.107263+00:00
-- url     : https://prove2.me/theorems/0d025cdf-80b3-4135-82d5-d94b2f8c7c46
-- title:
--   True original stopped UBV terminal L1 from linear growth at every finite horizon, arbitrary q
-- statement:
--   True original infinite-variation stopped terminal L1 at any bounded genuine stopping time. Explicit linear candidate growth supplies an exponential envelope, and the original bounded-horizon source exponential moment is integrable at any real q. Original all-branch terminal sign gives two-sided L1, without the additional Esscher exponent condition ψ(θ)≤q.
-- source:
--   Proved original stopped source L1 at any q (P4-F), source UBV nonnegative terminal P4-E, source linear-to-exponential envelope P4-F.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_exact_stopped_W_Term_nonnegative_all_branches
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_linear_upper_growth_implies_exponential_envelope
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_terminal_L1_of_bounded_exp_growth_any_q
open MeasureTheory Filter Topology Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f_assembly_original_linear_growth_terminal_integrable_any_q
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
    (θ B L K : ℝ) (hθ : 0 ≤ θ)
    (hK : 0 ≤ K) (hB : B ≤ K) (hL : L ≤ K * θ)
    (hlinear : ∀ y : ℝ, 0 ≤ y → w y ≤ B + L * y) :
    Integrable Term P := by sorry
