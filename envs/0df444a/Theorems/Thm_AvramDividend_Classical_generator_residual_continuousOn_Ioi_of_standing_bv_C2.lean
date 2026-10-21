-- Prove2me | Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_Ioi_of_standing_bv_C2
-- name    : AvramDividend.Classical.generator_residual_continuousOn_Ioi_of_standing_bv_C2
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T04:07:16.215902+00:00
-- url     : https://prove2.me/theorems/40982a98-dd8c-4935-940e-77c7ded55f53
-- title:
--   The standing bounded-variation generator residual is continuous on the whole positive half-line
-- statement:
--   Let `X` be a spectrally negative Lévy process with the standing assumptions and of bounded variation, let `q > 0` and let `W` be its `q`-scale function. Suppose `W` is twice continuously differentiable on the whole positive half-line `(0, ∞)`. Then the generator residual `x ↦ (Γ W)(x) - q W(x)` is continuous on `(0, ∞)`. This is the whole-halfline form of the local continuity statement `generator_residual_continuousOn_Ioo_of_standing_bv_C2`, which is only known on a bounded open interval `(0, a)`; the passage from the bounded-interval statement to the half-line statement is the point of the lemma, and it is the hypothesis `hcont` of the bounded-variation branch theorem `scaleFunction_generator_q_harmonic_of_nonzero_factor_c_two_bounded_variation` and of the whole aggregator `scaleFunction_generator_q_harmonic_of_nonzero_factor`.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Lemma 4 and its proof: the q-scale function satisfies (Gamma - q) W = 0 on (0, c*), and the continuity of the generator residual on the whole positive half-line is the regularity needed to pass from an almost-everywhere statement to a pointwise one.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem generator_residual_continuousOn_Ioi_of_standing_bv_C2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hC2 : ContDiffOn ℝ 2 W (Ioi (0 : ℝ))) :
    ContinuousOn
      (fun x : ℝ => X.generator W x - q * W x) (Ioi (0 : ℝ)) := by sorry

end AvramDividend.Classical
