-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB172_original_zerojump_unboundedvariation_gaussian_sigma_pos
-- name    : AvramDividend.Classical.avram_gbB172_original_zerojump_unboundedvariation_gaussian_sigma_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T17:33:54.303203+00:00
-- url     : https://prove2.me/theorems/92da0324-aaf2-4083-831e-93071e7b95db
-- title:
--   Original zero-jump unbounded-variation Lévy input has strictly positive Gaussian coefficient
-- statement:
--   With Lévy measure identically zero, the bounded-variation condition reduces to zero Gaussian volatility. The original unbounded-variation hypothesis forces the Gaussian coefficient σ to be strictly positive. This is the nondegenerate quadratic-variation input for the original Gaussian local-time occupation theorem B169.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB172_original_zerojump_unboundedvariation_gaussian_sigma_pos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0) :
    0 < X.σ := by sorry
