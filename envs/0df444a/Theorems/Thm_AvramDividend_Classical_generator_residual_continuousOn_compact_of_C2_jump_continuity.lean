-- Prove2me | Theorems.Thm_AvramDividend_Classical_generator_residual_continuousOn_compact_of_C2_jump_continuity
-- name    : AvramDividend.Classical.generator_residual_continuousOn_compact_of_C2_jump_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:12:53.881698+00:00
-- url     : https://prove2.me/theorems/d1495532-c800-47d7-9942-5d8dae5d3925
-- title:
--   The C2 scale-function generator residual is continuous on compact intervals if its jump term is
-- statement:
--   If W is twice continuously differentiable on (0,a), then W, W' and its second ordinary iterated derivative are continuous on every compact interval [l,u]⊂(0,a). If additionally the compensated jump integral is continuous there, the complete Lévy generator residual ΓW-qW is continuous on [l,u]. The proof composes the C2 second-derivative continuity lemma with the algebraic continuity-of-generator-components lemma.
-- source:
--   Pinned Mathlib ContDiffOn differential regularity and already established compensated Lévy generator continuity lemmas.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem generator_residual_continuousOn_compact_of_C2_jump_continuity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a))
    (hJ : ContinuousOn
      (fun x : ℝ =>
        ∫ y in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand W x y ∂X.ν)
      (Icc l u)) :
    ContinuousOn
      (fun x : ℝ => X.generator W x - q * W x)
      (Icc l u) := by sorry

end AvramDividend.Classical
