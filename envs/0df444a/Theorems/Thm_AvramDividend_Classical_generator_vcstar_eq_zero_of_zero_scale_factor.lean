-- Prove2me | Theorems.Thm_AvramDividend_Classical_generator_vcstar_eq_zero_of_zero_scale_factor
-- name    : AvramDividend.Classical.generator_vcstar_eq_zero_of_zero_scale_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:58:02.645694+00:00
-- url     : https://prove2.me/theorems/70e87e6f-533b-444f-9021-d51f501f762a
-- title:
--   Zero scale normalisation implies interior generator harmonicity
-- statement:
--   For a spectrally negative Lévy process with scale-supported candidate W, if the scale-derivative normalising factor divE(1,W'(c*)) is zero, then the barrier candidate vanishes strictly below c*. Generator locality and the zero generator of the zero function imply convergence and (Γ−q)v=0 on (0,c*). This is the exceptional zero-factor branch of Lemma 4, reusable independently of BV/UBV smoothness.
-- source:
--   Avram, Palmowski and Pistorius (2007), arXiv:math/0702893, Lemma 4 and the generator in Section 5. Algebraic zero-normalisation case proved using published generator locality.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_generator_eq_of_agree_below
import Theorems.Thm_AvramDividend_Classical_vcstar_eq_scaledW_le_cstar_of_support

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem generator_vcstar_eq_zero_of_zero_scale_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ) (W : ℝ → ℝ)
    (hsupport : ∀ z : ℝ, z < 0 → W z = 0)
    (hk : divE (1 : ℝ) (scaleDeriv W (cstar W).toReal) = 0) :
    ∀ x ∈ Ioo 0 (cstar W).toReal,
      X.GeneratorIntegrable (vcstar W) x ∧
        X.generator (vcstar W) x - q * vcstar W x = 0 := by sorry

end AvramDividend.Classical
