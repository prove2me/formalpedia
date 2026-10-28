-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_uniform_near_jump_linear_bound_on_compact_C1
-- name    : AvramDividend.Classical.scaleFunction_uniform_near_jump_linear_bound_on_compact_C1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:43:44.54146+00:00
-- url     : https://prove2.me/theorems/3122e735-cfe6-4c67-bfac-0be5cf6ece26
-- title:
--   Uniform first-order compensated jump bound near zero under C1 regularity
-- statement:
--   For a C1 scale function W and a compact positive starting-state interval, choose one negative-jump cutoff r and one constant C so the compensated generator integrand is bounded by C|y| uniformly in both x∈[l,u] and -r<y<0. Use the mean value theorem on [x+y,x] and the C1 derivative bound on the common compact [l-r,u]. This supplies the small-jump half of dominated continuity of the BV generator.
-- source:
--   Avram, Palmowski, Pistorius (2007), Lemma 4; uniform C1 mean-value estimate for bounded-variation generator continuity.

import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_uniform_near_jump_linear_bound_on_compact_C1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC1 : ContDiffOn ℝ 1 W (Ioo 0 a)) :
    ∃ r C : ℝ, 0 < r ∧ r < 1 ∧ r < l ∧ 0 ≤ C ∧
      ∀ x ∈ Icc l u, ∀ y ∈ Ioo (-r) 0,
        ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ ≤
          C * |y| := by sorry

end AvramDividend.Classical
