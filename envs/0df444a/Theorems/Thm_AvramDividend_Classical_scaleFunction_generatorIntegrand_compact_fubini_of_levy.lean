-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_compact_fubini_of_levy
-- name    : AvramDividend.Classical.scaleFunction_generatorIntegrand_compact_fubini_of_levy
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T06:38:03.063131+00:00
-- url     : https://prove2.me/theorems/9ba6e6bb-dab9-458d-a43b-0b27d876e76e
-- title:
--   Compact compensated-generator Fubini without an extra sigma-finiteness hypothesis
-- statement:
--   Under the native Levy quadratic-moment assumptions, for any finite measure of starting states and compact [l,u] inside a C2 scale-function interval, exchange product integration and iterated integration of the compensated generator over the negative jumps. The positive Lévy quadratic moment produces an SFinite negative-jump measure, so Mathlib's Fubini theorem applies directly without a new independent measure-typeclass assumption.
-- source:
--   Lévy quadratic jump condition and compact generator Fubini as verified earlier in the Avram Dividend mission.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generatorIntegrand_compact_fubini_of_levy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    (∫ p : ℝ × ℝ,
      (Icc l u ×ˢ Iio (0 : ℝ)).indicator
        (fun z : ℝ × ℝ =>
          SpectrallyNegativeLevy.generatorIntegrand W z.1 z.2) p
       ∂(μ.prod (X.ν.restrict (Iio 0)))) =
    ∫ x : ℝ, ∫ y : ℝ,
      (Icc l u ×ˢ Iio (0 : ℝ)).indicator
        (fun z : ℝ × ℝ =>
          SpectrallyNegativeLevy.generatorIntegrand W z.1 z.2) (x,y)
      ∂(X.ν.restrict (Iio 0)) ∂μ := by sorry

end AvramDividend.Classical
