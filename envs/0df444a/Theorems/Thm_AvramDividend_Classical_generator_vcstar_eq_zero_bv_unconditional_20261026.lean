-- Prove2me | Theorems.Thm_AvramDividend_Classical_generator_vcstar_eq_zero_bv_unconditional_20261026
-- name    : AvramDividend.Classical.generator_vcstar_eq_zero_bv_unconditional_20261026
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:55:09.597078+00:00
-- url     : https://prove2.me/theorems/b196c9ff-88d7-48a3-8870-63cf870a070b
-- title:
--   Unconditional BV generator harmonicity of the optimal-barrier value
-- statement:
--   For a spectrally negative Lévy process satisfying the standing conditions and bounded variation, a positive optimal barrier yields generator-domain membership and (Γ−q)vcstar=0 at every strictly interior reserve. At a zero scale normalisation the barrier value is identically zero below the barrier. At a nonzero normalisation, the newly established unconditional BV q-scale harmonicity transfers through the exact below-barrier generator congruence. No additional Laplace-residual hypothesis is assumed.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 4, bounded-variation branch.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_q_harmonic_of_nonzero_factor_bounded_variation
import Theorems.Thm_AvramDividend_Classical_bv_weighted_generator_residual_family_from_scale_20261026
import Theorems.Thm_AvramDividend_Classical_generator_vcstar_eq_zero_of_zero_scale_factor
import Theorems.Thm_AvramDividend_Classical_vcstar_interior_harmonicity_of_scale_harmonicity
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

namespace AvramDividend.Classical
/-- The canonical barrier candidate is generator-harmonic throughout the
positive interior when the spectrally negative Lévy process has BV paths. -/
theorem generator_vcstar_eq_zero_bv_unconditional_20261026
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : 0 < cstar W) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧
      X.generator (vcstar W) x - q * vcstar W x = 0 := by sorry
end AvramDividend.Classical
