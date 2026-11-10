-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf15_original_intrinsic_limit_ae_adapted_of_cutoff_convergence
-- name    : AvramDividend.Classical.avram_mix_inf15_original_intrinsic_limit_ae_adapted_of_cutoff_convergence
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T12:55:19.84979+00:00
-- url     : https://prove2.me/theorems/6ad44f7f-92ca-454c-9405-dc00ea99d580
-- title:
--   Original-filtration adaptedness of an infinite-activity Gaussian residual cutoff limit
-- statement:
--   For the actual spectrally negative Lévy process, a right-continuous-filtration measurable sequence of intrinsic truncated Gaussian residual fields with a common almost-sure all-time limit yields an adapted (almost-everywhere strongly measurable) limiting residual at every time. There is no finite-activity hypothesis; establishing the almost-sure convergence is a separate weighted-annulus L² and maximal inequality obligation.
-- source:
--   Noncircular generalisation of Proved a70e016c-54c1-4cfc-8e42-9152dedaee9e for f5e6e083 infinite activity: remove its hFinite by taking actual cutoff convergence as a separate premise. This theorem isolates original rightCont filtration measurability and does not assert cutoff convergence, martingale bracket, or Gaussian independent increments.

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_mix_inf15_original_intrinsic_limit_ae_adapted_of_cutoff_convergence
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hCut : ∀ (n : ℕ) (T : ℝ≥0),
      Measurable[𝓕.rightCont T]
        (fun ω : Ω => avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω))
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ T : ℝ≥0,
      Tendsto
        (fun n : ℕ => avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω)
        atTop (nhds (R T ω))) :
    ∀ T : ℝ≥0, AEStronglyMeasurable[𝓕.rightCont T] (R T) P := by sorry
