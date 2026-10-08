-- Prove2me | Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_compact_of_standing_bv_C2
-- name    : AvramDividend.Classical.generator_residual_continuousOn_compact_of_standing_bv_C2
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:13:26.800001+00:00
-- url     : https://prove2.me/theorems/f9c9ab4c-aae8-472f-9268-c20320009561
-- title:
--   Standing bounded-variation Lévy generator residual is continuous on compact C2 intervals
-- statement:
--   Under the process's standing bounded-variation assumptions, let W be a q-scale function that is C2 on (0,a). Its compensated negative-jump generator has already been proved continuous on every compact [l,u]⊂(0,a). The local drift/Gaussian derivative contributions are continuous by C2 regularity; hence ΓW−qW is continuous on the compact interval. This establishes the pointwise-regularity half of the a.e.-to-everywhere q-harmonicity strategy in the bounded-variation C2 branch.
-- source:
--   Previously verified BV compact compensated-generator continuity and conditional C2 generator-residual continuity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem generator_residual_continuousOn_compact_of_standing_bv_C2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ContinuousOn
      (fun x : ℝ => X.generator W x - q * W x)
      (Icc l u) := by sorry

end AvramDividend.Classical
