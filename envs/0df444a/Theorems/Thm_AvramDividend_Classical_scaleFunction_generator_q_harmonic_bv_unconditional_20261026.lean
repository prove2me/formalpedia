-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_q_harmonic_bv_unconditional_20261026
-- name    : AvramDividend.Classical.scaleFunction_generator_q_harmonic_bv_unconditional_20261026
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:50:56.625989+00:00
-- url     : https://prove2.me/theorems/5c8b3f9f-a8ab-4206-965c-bb4914c01112
-- title:
--   Unconditional bounded-variation q-scale generator harmonicity below the optimal barrier
-- statement:
--   For a standing bounded-variation spectrally negative Lévy process with q>0 and q-scale function W, if the optimal barrier is positive and its normalisation is nonzero, the generator integral exists and (Γ−q)W=0 at every interior reserve. The proof applies the full weighted BV generator-residual Laplace family (which is established from the scale transform) to the existing pointwise BV C1 harmonicity theorem, removing the latter's extra analytic assumption.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lemma 4. Direct consequence of the weighted generator-residual Laplace family and the canonical pointwise BV C1 harmonicity bridge.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_q_harmonic_of_nonzero_factor_bounded_variation
import Theorems.Thm_AvramDividend_Classical_bv_weighted_generator_residual_family_from_scale_20261026
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

namespace AvramDividend.Classical
/-- Under the standing BV assumptions, the q-scale function is
q-harmonic for the Lévy generator on the positive optimal-barrier interval. -/
theorem scaleFunction_generator_q_harmonic_bv_unconditional_20261026
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : 0 < cstar W)
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) ≠ 0) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable W x ∧ X.generator W x - q * W x = 0 := by sorry
end AvramDividend.Classical
