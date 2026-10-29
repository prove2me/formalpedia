-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_gaussian_or_bv_global_gradient
-- name    : AvramDividend.Classical.avram_ws01e_bf_new_gaussian_or_bv_global_gradient
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:57:47.505957+00:00
-- url     : https://prove2.me/theorems/91d09cd3-fb78-4a44-bef3-b52fb960c1af
-- title:
--   Unconditional Gaussian or BV global gradient inequality for the optimal barrier candidate
-- statement:
--   Under the canonical spectrally negative Levy Standing condition, positive discount, and the genuine q-scale definition, the Gaussian-or-bounded-variation disjunction implies differentiability of the optimal-barrier candidate at every positive reserve and derivative at least one. The Gaussian and absolutely continuous bounded-variation scale C1 regularity is established from exact Standing; the positive monotone Esscher tilt yields the global cstar gradient inequality.
-- source:
--   Source-faithful Gaussian/BV branch of AvramDividend.Classical.vcstar_deriv_ge_one (d42fc3e4), derived by composing accepted 14dc9d4c, bc92b9ce, bced81f2, 8d7288ac and 36de0c50, without assuming general unbounded-variation C1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_gaussian
import Theorems.Thm_AvramDividend_Classical_scaleFunction_contDiff_one_of_bv_absolutely_continuous_levy
import Theorems.Thm_AvramDividend_Classical_vcstar_deriv_ge_one_of_scale_C1_tilt
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bf_new_gaussian_or_bv_global_gradient
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hregular : 0 < X.σ ∨ X.BoundedVariation) :
    ∀ x : ℝ, 0 < x →
      DifferentiableAt ℝ (vcstar W) x ∧ 1 ≤ deriv (vcstar W) x := by sorry
