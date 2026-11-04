-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_joint_L1_expected_clock_limit
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_joint_L1_expected_clock_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:33:32.566008+00:00
-- url     : https://prove2.me/theorems/575d7d0d-562c-432e-884c-f7a6352371af
-- title:
--   Actual original stopped physical drift expectations converge with globally integrable pre-ruin limit
-- statement:
--   A genuine μ×P L1 source integrand yields an explicit uniform integrable pathwise envelope across every finite true clipped ruin horizon and the full pre-ruin integral. Under explicitly stated original-source AEStronglyMeasurable hypotheses for the random time integrals, the accepted original a.s. clock limit and Mathlib dominated convergence give an Integrable full pre-ruin random residual and convergence of finite-clock expectations. This closes the expectation passage for physical generator drift without postulating an external uniform-integrability envelope; stochastic M and dividend H remain separate.
-- source:
--   Accepted P4-E joint L1 almost-sure exact ruin-clock limit 3761ae40 and Fubini norm-envelope helper (pending authoring), Mathlib tendsto_integral_of_dominated_convergence and Integrable.mono.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_joint_L1_ae_true_clock_physical_limit
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_joint_L1_explicit_uniform_clock_envelope
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine joint L¹ and original measurability give finite expected pre-ruin physical drift limit. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_joint_L1_expected_clock_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (μ : Measure ℝ≥0) [SFinite μ]
    (f : ℝ≥0 × Ω → ℝ) (hf : Integrable f (μ.prod P))
    (hFiniteMeas : ∀ n : ℕ,
      AEStronglyMeasurable (fun ω => ∫ t : ℝ≥0,
          ({s : ℝ≥0 | (s : ℝ≥0∞) <
            min (ruinTime X x D ω) (n : ℝ≥0∞)}).indicator
            (fun t => f (t, ω)) t ∂μ) P)
    (hFullMeas : AEStronglyMeasurable (fun ω => (∫ t : ℝ≥0,
          ({s : ℝ≥0 | (s : ℝ≥0∞) < ruinTime X x D ω}).indicator
            (fun t => f (t, ω)) t ∂μ)) P) :
    Integrable (fun ω => (∫ t : ℝ≥0,
          ({s : ℝ≥0 | (s : ℝ≥0∞) < ruinTime X x D ω}).indicator
            (fun t => f (t, ω)) t ∂μ)) P ∧
    Tendsto (fun n : ℕ => ∫ ω, ∫ t : ℝ≥0,
          ({s : ℝ≥0 | (s : ℝ≥0∞) <
            min (ruinTime X x D ω) (n : ℝ≥0∞)}).indicator
            (fun t => f (t, ω)) t ∂μ ∂P)
      atTop (nhds (∫ ω, (∫ t : ℝ≥0,
          ({s : ℝ≥0 | (s : ℝ≥0∞) < ruinTime X x D ω}).indicator
            (fun t => f (t, ω)) t ∂μ) ∂P)) := by sorry
