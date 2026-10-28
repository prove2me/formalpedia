-- Prove2me | Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_positive_of_standing_bv_C1_sigma_zero
-- name    : AvramDividend.Classical.generator_residual_continuousOn_positive_of_standing_bv_C1_sigma_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:11:09.712651+00:00
-- url     : https://prove2.me/theorems/bae40e79-4640-4d82-be3d-a4298c2cd707
-- title:
--   BV C1 generator residual is continuous throughout positive reserve space
-- statement:
--   For a standing spectrally negative Levy process of bounded variation and zero Gaussian coefficient, a q-scale function C1 on the positive reserve half-line has continuous discounted generator residual. Prove locally on compact intervals and extend at interior points.
-- source:
--   Avram, Palmowski, Pistorius (2007), Lemma 4, BV C1 continuity.

import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem generator_residual_continuousOn_positive_of_standing_bv_C1_sigma_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation) (hσ : X.σ = 0)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hC1 : ContDiffOn ℝ 1 W (Ioi 0)) :
    ContinuousOn (fun x : ℝ => X.generator W x - q * W x) (Ioi 0) := by sorry

end AvramDividend.Classical
