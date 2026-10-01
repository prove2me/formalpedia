-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generator_eq_zero
-- name    : AvramDividend.Classical.scaleFunction_generator_eq_zero
-- status  : Open
-- author  : @WillR
-- created : 2026-09-30T18:16:27.305506+00:00
-- url     : https://prove2.me/theorems/d321a25e-e5a5-4415-937a-b173fd7712a5
-- title:
--   The q-scale function is q-harmonic for the Lévy generator
-- statement:
--   On a positive interval where the q-scale function is sufficiently smooth for the appropriate Itô formula, it lies in the generator domain and satisfies (Γ-q)W^(q)=0. This is the generator form of the standard q-harmonicity of the scale function killed at zero.
-- source:
--   Avram, Palmowski and Pistorius, arXiv:math/0702893v1, equation (3.7), where the stopped discounted q-scale function is stated to be a martingale, together with the proof of Lemma 4, p. 21, which applies the appropriate Itô/change-of-variables formula under sufficient smoothness to conclude (Γ-q)W^(q)=0 on the interior.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generator_eq_zero {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) (a : ℝ) (ha : 0 < a)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ∀ x ∈ Ioo 0 a,
      X.GeneratorIntegrable W x ∧ X.generator W x - q * W x = 0 := by sorry

end AvramDividend.Classical
