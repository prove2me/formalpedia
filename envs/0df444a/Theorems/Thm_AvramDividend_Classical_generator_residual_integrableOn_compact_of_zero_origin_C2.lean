-- Prove2me | Theorems.Thm_AvramDividend_Classical_generator_residual_integrableOn_compact_of_zero_origin_C2
-- name    : AvramDividend.Classical.generator_residual_integrableOn_compact_of_zero_origin_C2
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T11:09:12.326979+00:00
-- url     : https://prove2.me/theorems/561936a2-3072-4419-aa4e-7195578d34cd
-- title:
--   Zero-origin q-scale generator residual integrable on compact C2 state intervals
-- statement:
--   For any q-scale function W vanishing at 0 and C2 on (0,a), the compensated Lévy generator residual ΓW−qW is integrable over every compact subinterval against every finite state measure, with no Lévy atomlessness hypothesis. It follows from the already proved zero-origin compensated generator continuity theorem and the compact-continuity integrability theorem. Intended for localised weak generator and occupation-measure identities.
-- source:
--   Accepted zero-origin compact generator residual continuity and finite-measure compact integrability theorem.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem generator_residual_integrableOn_compact_of_zero_origin_C2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (μ : Measure ℝ) [IsFiniteMeasure μ] :
    IntegrableOn (fun x : ℝ => X.generator W x - q * W x)
      (Icc l u) μ := by sorry

end AvramDividend.Classical
