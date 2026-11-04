-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_joint_L1_explicit_uniform_clock_envelope
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_joint_L1_explicit_uniform_clock_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:12:13.932471+00:00
-- url     : https://prove2.me/theorems/8d89b2a9-3032-46fe-adab-3502d64ef363
-- title:
--   Genuine original joint L1 constructs an integrable pathwise envelope for every clipped ruin clock
-- statement:
--   For the actual original controlled reserve X,D and exact min(ruinTime,n) clocks, any genuine globally Integrable f under μ×P yields a single sample-wise physical-time norm envelope B(ω)=∫‖f(t,ω)‖ dμ. Pinned Fubini proves B is Integrable P, and the Bochner norm integral inequality proves all finite ruin-clipped integrals and the full pre-ruin integral are bounded by B almost surely. This is a source-backed uniform integrability bound for physical drift, not a stochastic-martingale statement.
-- source:
--   Mathlib pinned MeasureTheory.Integrable.integral_norm_prod_right, Integrable.prod_left_ae and norm_integral_le_of_norm_le; original ruinTime and actual D.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine joint L¹ supplies a single integrable source-clock envelope for every horizon. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_joint_L1_explicit_uniform_clock_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (μ : Measure ℝ≥0) [SFinite μ]
    (f : ℝ≥0 × Ω → ℝ) (hf : Integrable f (μ.prod P)) :
    Integrable (fun ω => (∫ t : ℝ≥0, ‖f (t, ω)‖ ∂μ)) P ∧
    ∀ᵐ ω ∂P,
      (∀ n : ℕ, ‖(∫ t : ℝ≥0,
        ({s : ℝ≥0 | (s : ℝ≥0∞) <
          min (ruinTime X x D ω) (n : ℝ≥0∞)}).indicator
          (fun t => f (t, ω)) t ∂μ)‖ ≤ (∫ t : ℝ≥0, ‖f (t, ω)‖ ∂μ)) ∧
      ‖(∫ t : ℝ≥0,
        ({s : ℝ≥0 | (s : ℝ≥0∞) < ruinTime X x D ω}).indicator
          (fun t => f (t, ω)) t ∂μ)‖ ≤ (∫ t : ℝ≥0, ‖f (t, ω)‖ ∂μ) := by sorry
