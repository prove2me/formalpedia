-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_mixed11_mean_to_signed_of_expected
-- name    : AvramDividend.Classical.avram_ubv_mixed11_mean_to_signed_of_expected
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T08:19:26.059894+00:00
-- url     : https://prove2.me/theorems/bd114eef-4213-4885-a478-429ed1d4d4e1
-- title:
--   Original probability-space expected upper bound gives three centred signed source components
-- statement:
--   For an integrable reward Z on the same probability space as an original spectrally negative Levy process X, an expected upper bound yields a source-exact signed certificate with three integrable zero-mean components and two almost-surely nonpositive residuals. It uses the already proved original-L1 assembly theorem b77e6dae. This algebraic lifting does not assert an Ito-Meyer decomposition or establish the physical mixed-process expectation bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_expected_budget_witness_of_original_L1

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

theorem AvramDividend.Classical.avram_ubv_mixed11_mean_to_signed_of_expected
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (Z : Ω → ℝ) (hZI : Integrable Z P) (b : ℝ)
    (hBudget : (∫ ω, Z ω ∂P) ≤ b) :
    ∃ Mc Ms Ml G R : Ω → ℝ,
      Integrable Mc P ∧ Integrable Ms P ∧ Integrable Ml P ∧
      (∫ ω, Mc ω ∂P) = 0 ∧
      (∫ ω, Ms ω ∂P) = 0 ∧
      (∫ ω, Ml ω ∂P) = 0 ∧
      (∀ᵐ ω ∂P, G ω ≤ 0) ∧ (∀ᵐ ω ∂P, R ω ≤ 0) ∧
      (∀ᵐ ω ∂P,
        Z ω ≤ b + Mc ω + Ms ω + Ml ω + G ω + R ω) := by
  sorry
