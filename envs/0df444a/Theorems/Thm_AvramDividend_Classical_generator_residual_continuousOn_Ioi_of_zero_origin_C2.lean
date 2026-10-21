-- Prove2me | Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_Ioi_of_zero_origin_C2
-- name    : AvramDividend.Classical.generator_residual_continuousOn_Ioi_of_zero_origin_C2
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T04:44:14.706882+00:00
-- url     : https://prove2.me/theorems/1fe801dd-dcf1-4433-8d62-a8bb5b06dc44
-- title:
--   The zero-origin generator residual is continuous on the whole positive half-line
-- statement:
--   Let `X` be a spectrally negative Lévy process, let `q > 0` and let `W` be its `q`-scale function. Suppose the scale function vanishes at the origin and is twice continuously differentiable on the whole positive half-line `(0, ∞)`. Then the generator residual `x ↦ (Γ W)(x) - q W(x)` is continuous on `(0, ∞)`. This is the whole-halfline form of the local continuity statement `generator_residual_continuousOn_compact_of_zero_origin_C2`, and it is the hypothesis `hcont` of the prescribed `C²` branch theorem `scaleFunction_generator_q_harmonic_of_nonzero_factor_c_two_standing` and of the whole aggregator `scaleFunction_generator_q_harmonic_of_nonzero_factor`. It is the zero-origin counterpart of the bounded-variation statement `generator_residual_continuousOn_Ioi_of_standing_bv_C2`.
-- source:
--   Avram, Palmowski, Pistorius, On the optimal dividend problem for a spectrally negative Levy process, arXiv:math/0702893v1, Lemma 4 and its proof: the q-scale function satisfies (Gamma - q) W = 0 on (0, c*), and the continuity of the generator residual on the whole positive half-line is the regularity needed to pass from an almost-everywhere statement to a pointwise one.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem generator_residual_continuousOn_Ioi_of_zero_origin_C2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (hC2 : ContDiffOn ℝ 2 W (Ioi (0 : ℝ))) :
    ContinuousOn
      (fun x : ℝ => X.generator W x - q * W x) (Ioi (0 : ℝ)) := by sorry

end AvramDividend.Classical
