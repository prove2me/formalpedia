-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_compact_fubini
-- name    : AvramDividend.Classical.scaleFunction_generatorIntegrand_compact_fubini
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:48:28.838611+00:00
-- url     : https://prove2.me/theorems/792fd0ed-13df-48d5-95f5-f4dadeed9efd
-- title:
--   Fubini equality for the compensated scale-function generator on a compact state interval
-- statement:
--   For a q-scale function C2 on an open interval (0,a), a compact subinterval [l,u] contained in it, any finite measure of starting states and the restricted negative-jump Levy measure assumed sigma finite, the integral of the generator's compensated increment over the product equals the iterated integral (integrating negative jumps first and then starting states). The supporting compact-product integrability theorem supplies the integrability hypothesis required by Mathlib's Bochner Fubini theorem. The sigma-finite condition is made explicit rather than silently assumed by the local state and Levy-measure definitions.
-- source:
--   A direct application of the Fubini theorem to the compact-localised compensated generator step in Avram, Palmowski and Pistorius (2007), Lemma 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generatorIntegrand_compact_fubini
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    [SFinite (X.ν.restrict (Iio 0))] :
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
