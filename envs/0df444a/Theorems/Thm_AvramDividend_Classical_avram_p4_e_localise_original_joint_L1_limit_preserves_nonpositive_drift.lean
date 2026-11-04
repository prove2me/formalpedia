-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_joint_L1_limit_preserves_nonpositive_drift
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_joint_L1_limit_preserves_nonpositive_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T13:09:50.460916+00:00
-- url     : https://prove2.me/theorems/67b41962-f76b-43f8-a180-bf1694ec0406
-- title:
--   Original exact ruin-stopped signed physical drift remains nonpositive under genuine joint L1 localisation
-- statement:
--   Given actual original source jointly integrable physical-time/probability integrand f, all countably many exact min(ruin,n) stopped time integrals are nonpositive almost surely. The compiler-accepted original clock Fubini/DCT helper yields a.s. convergence, while ae_all_iff gives one common P-conull event for all n. The limit pre-ruin integral is therefore nonpositive almost surely. This concerns physical generator drift, not stochastic martingale optional stopping or dividend Stieltjes atoms.
-- source:
--   Accepted P4-E exact source clock DCT 6687d899 and original joint L1 a.e. limit 3761ae40; Mathlib ae_all_iff/le_of_tendsto.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_joint_L1_ae_true_clock_physical_limit
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original ruin-stopped nonpositive physical drift survives the a.s. clock limit. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_joint_L1_limit_preserves_nonpositive_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [SFinite P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (μ : Measure ℝ≥0) [SFinite μ]
    (f : ℝ≥0 × Ω → ℝ) (hf : Integrable f (μ.prod P))
    (hNonpos : ∀ n : ℕ, ∀ᵐ ω ∂P,
      (∫ t : ℝ≥0,
          ({s : ℝ≥0 | (s : ℝ≥0∞) <
            min (ruinTime X x D ω) (n : ℝ≥0∞)}).indicator
            (fun t => f (t, ω)) t ∂μ) ≤ 0) :
    ∀ᵐ ω ∂P, (∫ t : ℝ≥0,
          ({s : ℝ≥0 | (s : ℝ≥0∞) < ruinTime X x D ω}).indicator
            (fun t => f (t, ω)) t ∂μ) ≤ 0 := by sorry
