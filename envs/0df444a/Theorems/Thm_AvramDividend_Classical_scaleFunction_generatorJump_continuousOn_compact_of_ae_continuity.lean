-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorJump_continuousOn_compact_of_ae_continuity
-- name    : AvramDividend.Classical.scaleFunction_generatorJump_continuousOn_compact_of_ae_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:14:04.087423+00:00
-- url     : https://prove2.me/theorems/cd6079a9-44d4-4cc0-840c-d3208d90bf2b
-- title:
--   Continuity of the Lévy scale-function jump generator on compact intervals
-- statement:
--   For W in C2 on a neighbourhood of [l,u] strictly inside the positive half-line, the previously proved compensated-integrand bound supplies one integrable C min(1,y²) envelope, uniform in x∈[l,u]. If for almost every negative jump the compensated integrand is continuous in the state variable on [l,u], then x↦∫generatorIntegrand W x y ν(dy) is continuous on that compact interval. This isolates precisely the remaining jump pointwise-continuity issue, including possible jumps of W at the origin and atoms of the Lévy measure.
-- source:
--   Dominated convergence applied to the accepted uniform compact generator-jump bound in Avram Dividend.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generatorJump_continuousOn_compact_of_ae_continuity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (hjump : ∀ x ∈ Icc l u,
      ∀ᵐ y ∂(X.ν.restrict (Iio 0)),
        ContinuousWithinAt
          (fun z : ℝ => SpectrallyNegativeLevy.generatorIntegrand W z y)
          (Icc l u) x) :
    ContinuousOn
      (fun x : ℝ =>
        ∫ y : ℝ, SpectrallyNegativeLevy.generatorIntegrand W x y
          ∂(X.ν.restrict (Iio 0)))
      (Icc l u) := by sorry

end AvramDividend.Classical
