-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorJump_continuousOn_compact_of_standing_bv
-- name    : AvramDividend.Classical.scaleFunction_generatorJump_continuousOn_compact_of_standing_bv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:29:13.406194+00:00
-- url     : https://prove2.me/theorems/a5eef9d6-22a5-48c1-a99f-9e2b1193cf9b
-- title:
--   BV scale-function jump generator is continuous on compact C2 intervals
-- statement:
--   Under the standing bounded-variation assumptions and local C2 regularity of the q-scale function W, the negative-jump part of the compensated Lévy generator is a continuous function of the state on every compact interval inside the smoothness region. This combines atomlessness of the Lévy measure, almost-everywhere jumpwise state continuity, uniform quadratic domination of the compensated increment, and the dominated-convergence theorem. It is a nontrivial local regularity input for identifying the q-harmonic generator residual.
-- source:
--   The proved compact dominated-convergence generator theorem and the BV atomlessness continuity reduction in the Avram Dividend mission.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generatorJump_continuousOn_compact_of_standing_bv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ContinuousOn
      (fun x : ℝ =>
        ∫ y : ℝ, SpectrallyNegativeLevy.generatorIntegrand W x y
          ∂(X.ν.restrict (Iio 0)))
      (Icc l u) := by sorry

end AvramDividend.Classical
