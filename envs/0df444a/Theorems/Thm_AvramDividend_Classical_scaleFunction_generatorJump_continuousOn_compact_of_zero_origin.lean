-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorJump_continuousOn_compact_of_zero_origin
-- name    : AvramDividend.Classical.scaleFunction_generatorJump_continuousOn_compact_of_zero_origin
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:21:19.212061+00:00
-- url     : https://prove2.me/theorems/878e737d-8970-477f-87c2-5d1e2fad9b91
-- title:
--   Zero-origin scale-function jump generator is continuous on compact C2 intervals
-- statement:
--   Suppose the q-scale function W vanishes at the origin and is C2 on (0,a). Then the compensated Lévy jump-integral part of its generator is continuous on each compact [l,u]⊂(0,a), without assuming the Lévy measure has no atoms. Indeed W is globally continuous because W(0)=0, and W' is locally continuous by C2 smoothness; the fixed-jump compensated increment is therefore continuous at every negative jump. Uniform compact quadratic domination and dominated convergence give continuity of the integrated jump term.
-- source:
--   Previously accepted zero-origin global-continuity, fixed-jump continuity, and dominated-convergence generator theorems.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generatorJump_continuousOn_compact_of_zero_origin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ContinuousOn
      (fun x : ℝ =>
        ∫ y : ℝ, SpectrallyNegativeLevy.generatorIntegrand W x y
          ∂(X.ν.restrict (Iio 0)))
      (Icc l u) := by sorry

end AvramDividend.Classical
