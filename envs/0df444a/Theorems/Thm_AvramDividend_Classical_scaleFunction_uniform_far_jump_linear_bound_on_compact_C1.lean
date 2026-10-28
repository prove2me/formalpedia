-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_uniform_far_jump_linear_bound_on_compact_C1
-- name    : AvramDividend.Classical.scaleFunction_uniform_far_jump_linear_bound_on_compact_C1
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:42:23.11354+00:00
-- url     : https://prove2.me/theorems/8af2f18e-a2fe-407f-a009-4a5b9097f20c
-- title:
--   Uniform first-order compensated jump bound away from zero under C1 regularity
-- statement:
--   For C1 scale function W, compact capital interval inside (0,a), and positive negative-jump cutoff r, one constant uniformly bounds the compensated generator integrand for all capital x in the compact interval and all y≤-r, by C min(1,|y|). Uses monotonicity and support of W, a uniform compact bound on W', and the compensation indicator. A first-order bound is integrable for bounded-variation Lévy measures.
-- source:
--   Avram, Palmowski, Pistorius (2007), Lemma 4; a C1 refinement of the Proved uniform C2 far-jump bound.

import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_uniform_far_jump_linear_bound_on_compact_C1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u r : ℝ)
    (hl : 0 < l) (hlu : l < u) (hu : u < a) (hr : 0 < r)
    (hC1 : ContDiffOn ℝ 1 W (Ioo 0 a)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Icc l u, ∀ y < 0, y ≤ -r →
        ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ ≤
          C * min 1 |y| := by sorry

end AvramDividend.Classical
