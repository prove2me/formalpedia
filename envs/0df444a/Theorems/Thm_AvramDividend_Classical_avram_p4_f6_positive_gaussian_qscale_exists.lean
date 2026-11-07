-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f6_positive_gaussian_qscale_exists
-- name    : AvramDividend.Classical.avram_p4_f6_positive_gaussian_qscale_exists
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T09:20:59.285976+00:00
-- url     : https://prove2.me/theorems/a9e3e12a-a8a2-4c91-ab81-3c6601755032
-- title:
--   Existence of a strictly positive-at-one q-scale function for the Gaussian Lévy branch
-- statement:
--   Every original spectrally negative Lévy process satisfying standing conditions with strictly positive Gaussian volatility has a q-scale function W for each positive discount q, and W(1)>0. This is a distinct existence input needed to apply the q-scale envelope and killed HJB comparison to the abstract candidate w, because the original analytic-growth theorem does not assume a scale function.
-- source:
--   Independent mathematical existence obligation for source 51922c24: scale function existence from the spectrally negative Lévy Laplace exponent and two-sided exit problem, separately from its already-proved conditional q-scale envelope b114eb46 and killed HJB comparison fe2d23f9.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f6_positive_gaussian_qscale_exists
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (hσ : 0 < X.σ) :
    ∃ W : ℝ → ℝ, IsScaleFunction X q W ∧ 0 < W 1 := by sorry
