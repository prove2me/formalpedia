-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsc_zerojump_ubv_original_affine_brownian_source
-- name    : AvramDividend.Classical.avram_lsc_zerojump_ubv_original_affine_brownian_source
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T17:53:39.320362+00:00
-- url     : https://prove2.me/theorems/b13f7426-f4b1-4571-94cc-ba4a638ed177
-- title:
--   Original Avram zero-jump UBV Lévy source equals drift plus Brownian diffusion on the same sample space
-- statement:
--   Under the exact original Avram unbounded-variation and zero-jump hypotheses, obtain a LevyStochCalc Brownian motion on the same probability space for which the entire original Lévy path equals deterministic drift plus Gaussian coefficient times that Brownian path at every real time, including the constant extension before time zero. Derive probability and positive Gaussian coefficient internally. This states the original-source SDE as a pointwise identity ready for the imported Brownian Itô calculus, without postulating an independent Brownian motion or changing probability space. The declared probability typeclass instance is supplied by the original SpectrallyNegativeLevy.isProbability field at every use.
-- source:
--   From Proved 05b01179-f449-4dd4-ab7a-ed44323d0879 and 37d963a0-712f-4f06-87d6-6a9238f0684c. Concrete affine source interface for the Gaussian branch 4aaca024 and Avram public stopped source fdb9a6a3. Source-facing application may synthesize the explicitly named IsProbabilityMeasure P from X.isProbability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_KLSModular_LevyStochCalc_Brownian_Construction
import Theorems.Thm_AvramDividend_Classical_avram_p4_f4_zero_levy_ubv_sigma_pos
import Theorems.Thm_AvramDividend_Classical_avram_lsc_zerojump_original_sameSpace_brownian
open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_lsc_zerojump_ubv_original_affine_brownian_source
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) :
    ∃ W : LevyStochCalc.Brownian.BrownianMotion P,
      ∀ (t : ℝ) (ω : Ω),
        X.X (Real.toNNReal t) ω =
          (Real.toNNReal t : ℝ) * X.c + X.σ * W.W t ω := by sorry
