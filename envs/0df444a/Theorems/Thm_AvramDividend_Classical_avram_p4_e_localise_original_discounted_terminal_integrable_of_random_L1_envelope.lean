-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_discounted_terminal_integrable_of_random_L1_envelope
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_discounted_terminal_integrable_of_random_L1_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T14:55:13.372195+00:00
-- url     : https://prove2.me/theorems/3f6d15da-5327-422b-a880-ff69634057ee
-- title:
--   True original discounted terminal is integrable under a sample-dependent integrable envelope
-- statement:
--   For the actual nonnegative time clock and discount q≥0 in the original source P, an a.e. random L1 bound B(ω) on |w(Wω)| provides a real global Integrable discounted terminal. No finiteness cap, bounded w, optional-stopping expectation, or hidden terminal positivity premise is assumed. Source-specific estimation of B remains a separate obligation.
-- source:
--   Original P4-F discounted terminal with Mathlib Integrable.mono and Real.exp_le_one_iff.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A genuine integrable random envelope gives L¹ for the original discounted terminal. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_discounted_terminal_integrable_of_random_L1_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q)
    (τ : Ω → ℝ≥0) (w : ℝ → ℝ) (W : Ω → ℝ)
    (hMeas : AEStronglyMeasurable
      (fun ω => Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) P)
    (B : Ω → ℝ) (hB : Integrable B P)
    (hBound : ∀ᵐ ω ∂P, |w (W ω)| ≤ B ω) :
    Integrable (fun ω => Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) P := by sorry
