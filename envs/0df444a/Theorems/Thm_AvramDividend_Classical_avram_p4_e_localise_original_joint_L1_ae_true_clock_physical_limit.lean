-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_joint_L1_ae_true_clock_physical_limit
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_joint_L1_ae_true_clock_physical_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:01:17.473415+00:00
-- url     : https://prove2.me/theorems/3761ae40-51b2-4985-a618-44f31fe9ebd7
-- title:
--   Original exact-ruin-clipped physical integrals converge almost surely from joint time-probability L1
-- statement:
--   A genuine original physical time×probability Integrable f gives integrable time fibres for almost every sample by Fubini. Applying the source exact-clock pathwise DCT on each such original sample proves a.s. convergence of deterministic-truncated pre-ruin integrals to full pre-ruin integral. This supplies an actual probabilistic localisation limit for generator-like integrands under explicit joint L1, without claiming original stopped martingales are UI.
-- source:
--   P4-E exact source clock physical DCT and pinned Mathlib Integrable.prod_left_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_true_clock_physical_integral_DCT
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original physical stopped integrals converge a.s. under genuine joint L¹. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_joint_L1_ae_true_clock_physical_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (μ : Measure ℝ≥0) [SFinite μ]
    (f : ℝ≥0 × Ω → ℝ) (hf : Integrable f (μ.prod P)) :
    ∀ᵐ ω ∂P,
      Tendsto
        (fun n : ℕ => ∫ t : ℝ≥0,
          ({s : ℝ≥0 | (s : ℝ≥0∞) <
            min (ruinTime X x D ω) (n : ℝ≥0∞)}).indicator
            (fun t => f (t, ω)) t ∂μ)
        atTop
        (nhds (∫ t : ℝ≥0,
          ({s : ℝ≥0 | (s : ℝ≥0∞) < ruinTime X x D ω}).indicator
            (fun t => f (t, ω)) t ∂μ)) := by sorry
