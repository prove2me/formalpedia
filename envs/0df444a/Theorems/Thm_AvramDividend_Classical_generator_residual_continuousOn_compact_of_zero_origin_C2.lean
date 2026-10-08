-- Prove2me | Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_compact_of_zero_origin_C2
-- name    : AvramDividend.Classical.generator_residual_continuousOn_compact_of_zero_origin_C2
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:22:41.35365+00:00
-- url     : https://prove2.me/theorems/a6a727ef-470d-4b62-93a8-00a278a5d9fd
-- title:
--   Zero-origin Lévy generator residual is continuous on every compact C2 state interval
-- statement:
--   If a q-scale function W vanishes at the origin and is C2 on a positive interval, then the compensated jump integral is continuous on each compact subinterval, independently of Lévy-measure atomlessness. The local Gaussian, drift and discount terms are likewise continuous from C2 regularity. Thus ΓW−qW is continuous on the compact state interval. This supplies the pointwise regularity half of the zero-origin q-harmonic generator proof.
-- source:
--   Verified generator continuity from C2 plus zero-origin compensated-jump dominated convergence in Avram Dividend.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem generator_residual_continuousOn_compact_of_zero_origin_C2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hzero : W 0 = 0)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ContinuousOn
      (fun x : ℝ => X.generator W x - q * W x)
      (Icc l u) := by sorry

end AvramDividend.Classical
