-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_uniform_linear_jump_bound_on_compact_C1
-- name    : AvramDividend.Classical.scaleFunction_uniform_linear_jump_bound_on_compact_C1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:44:49.80902+00:00
-- url     : https://prove2.me/theorems/e129c12c-3198-4279-ae45-9eb7efe0ba77
-- title:
--   Uniform min(1,|y|) jump generator domination on compact C1 intervals
-- statement:
--   Uniform in both starting state and negative-jump size, the compensated generator kernel of a C1 scale function is bounded by C min(1,|y|) on every compact subinterval of its C1 domain. Combine the separate near-zero linear and far-negative-jump linear bounds at a common cutoff r with C=max(Cnear,Cfar). This is the dominating function needed for bounded-variation Lévy generator continuity.
-- source:
--   Avram, Palmowski, Pistorius (2007), Lemma 4, bounded-variation C1 generator kernel domination.

import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_uniform_linear_jump_bound_on_compact_C1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC1 : ContDiffOn ℝ 1 W (Ioo 0 a)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Icc l u, ∀ y ∈ Iio (0 : ℝ),
        ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ ≤
          C * min 1 |y| := by sorry

end AvramDividend.Classical
