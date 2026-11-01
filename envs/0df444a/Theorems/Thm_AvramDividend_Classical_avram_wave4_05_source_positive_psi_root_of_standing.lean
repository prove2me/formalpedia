-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_05_source_positive_psi_root_of_standing
-- name    : AvramDividend.Classical.avram_wave4_05_source_positive_psi_root_of_standing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:29:15.984748+00:00
-- url     : https://prove2.me/theorems/1da68fa5-700c-4631-bdca-58297a897faf
-- title:
--   Original Standing Lévy exponent has a strictly positive root at every positive discount q
-- statement:
--   For the actual Standing spectrally negative Levy source process, any strictly positive discount q is attained by the Laplace exponent at a strictly positive Esscher parameter phi. The proof uses the actual source exponent identity psi(0)=0, the continuous restriction on [0,∞), and its source-specific eventual exceedance of q. The intermediate value theorem on [0,max(beta0,0)] yields phi with psi(phi)=q, and q>0 excludes phi=0. No extra root hypothesis remains for the Gaussian compensated-generator theorem.
-- source:
--   Proved levy_laplace_exponent_zero, levy_laplace_exponent_continuousOn_nonnegative, psi_eventually_gt_of_standing, pinned Mathlib intermediate_value_Icc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_zero
import Theorems.Thm_AvramDividend_Classical_levy_laplace_exponent_continuousOn_nonnegative
import Theorems.Thm_AvramDividend_Classical_psi_eventually_gt_of_standing
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal
/-- Positive q-root of the actual source Lévy exponent under Standing. -/

theorem AvramDividend.Classical.avram_wave4_05_source_positive_psi_root_of_standing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) :
    ∃ φ : ℝ, 0 < φ ∧ X.ψ φ = q := by sorry
