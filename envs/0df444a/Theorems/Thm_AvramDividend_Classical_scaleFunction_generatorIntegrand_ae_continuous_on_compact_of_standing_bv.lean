-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorIntegrand_ae_continuous_on_compact_of_standing_bv
-- name    : AvramDividend.Classical.scaleFunction_generatorIntegrand_ae_continuous_on_compact_of_standing_bv
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T07:28:39.516208+00:00
-- url     : https://prove2.me/theorems/b79e6db3-be60-4e30-91b0-97fb740e91c2
-- title:
--   BV Lévy jumps satisfy a.e. state continuity on compact C2 intervals
-- statement:
--   Under the standing bounded-variation Lévy conditions and local C2 regularity of W, for every x in a compact positive interval and almost every negative jump y, the compensated generator integrand is continuous within that interval as a function of x. Derivative continuity comes from C2 smoothness, W is continuous at each positive x, and the only possible discontinuity of W at the shifted state x+y is avoided almost surely because the Lévy measure has no atoms.
-- source:
--   The accepted generator fixed-jump continuity reduction and the standing bounded-variation Lévy atomlessness lemma.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generatorIntegrand_ae_continuous_on_compact_of_standing_bv
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ∀ x ∈ Icc l u,
      ∀ᵐ y ∂(X.ν.restrict (Iio 0)),
        ContinuousWithinAt
          (fun z : ℝ => SpectrallyNegativeLevy.generatorIntegrand W z y)
          (Icc l u) x := by sorry

end AvramDividend.Classical
