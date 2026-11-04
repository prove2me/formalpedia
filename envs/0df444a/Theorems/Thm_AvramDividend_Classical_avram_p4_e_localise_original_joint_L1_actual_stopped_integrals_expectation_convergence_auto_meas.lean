-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_joint_L1_actual_stopped_integrals_expectation_convergence_auto_meas
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_joint_L1_actual_stopped_integrals_expectation_convergence_auto_meas
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T15:19:02.260438+00:00
-- url     : https://prove2.me/theorems/96037762-d405-47e9-ae37-6abbf2056ca5
-- title:
--   Original controlled full ruin and finite-horizon signed physical expectations converge from joint L1 alone
-- statement:
--   For the actual original source controlled ruin clock and measurable dividend strategy, one genuine μ×P Integrable signed generator/residual density suffices to prove global integrability of its full pre-ruin physical integral and convergence of the expectations of every finite clipped clock. The original source ruinTime measurability discharges all probability-space strong measurability assumptions by exact stopped integral L1; the accepted source joint DCT and uniform envelope then give expectation convergence. No additional UI, zero endpoint occupation, or random Stieltjes atom assumption is inserted.
-- source:
--   P4-E source exact all-stopped L1 and joint L1 expected clock limit, pinned Mathlib Integrable.aestronglyMeasurable.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_joint_L1_all_stopped_integrals_integrable
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_joint_L1_expected_clock_limit
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Joint L¹ alone, with the original source dividend strategy, ensures physical stopped expectation convergence. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_joint_L1_actual_stopped_integrals_expectation_convergence_auto_meas
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (hDiv : IsDividendStrategy 𝓕 D)
    (μ : Measure ℝ≥0) [SFinite μ]
    (f : ℝ≥0 × Ω → ℝ) (hf : Integrable f (μ.prod P)) :
    Integrable (fun ω => ∫ t : ℝ≥0,
      ({s : ℝ≥0 | (s : ℝ≥0∞) < ruinTime X x D ω}).indicator
        (fun t => f (t, ω)) t ∂μ) P ∧
    Tendsto (fun n : ℕ => ∫ ω, ∫ t : ℝ≥0,
      ({s : ℝ≥0 | (s : ℝ≥0∞) <
        min (ruinTime X x D ω) (n : ℝ≥0∞)}).indicator
        (fun t => f (t, ω)) t ∂μ ∂P)
      atTop (nhds (∫ ω, ∫ t : ℝ≥0,
      ({s : ℝ≥0 | (s : ℝ≥0∞) < ruinTime X x D ω}).indicator
        (fun t => f (t, ω)) t ∂μ ∂P)) := by sorry
