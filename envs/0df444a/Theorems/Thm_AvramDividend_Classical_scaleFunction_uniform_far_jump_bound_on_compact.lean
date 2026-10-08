-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_uniform_far_jump_bound_on_compact
-- name    : AvramDividend.Classical.scaleFunction_uniform_far_jump_bound_on_compact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:35:03.969397+00:00
-- url     : https://prove2.me/theorems/25b17770-6fb1-467a-aca4-f9da2288a85f
-- title:
--   Uniform compensated-generator bound for far negative jumps on a compact state interval
-- statement:
--   Let W be a q-scale function that is C2 on (0,a). Fix a compact state interval [l,u] strictly inside (0,a), and a jump cutoff r>0. Then a single finite constant C>=0 bounds the generator's compensated negative-jump increment for every x in [l,u] and every y<=-r by C min(1,y^2). Monotonicity gives 0<=W(x+y)<=W(x)<=W(u), and the first derivative is uniformly bounded on [l,u] by compact C2 regularity. The compensation term is at most the derivative bound because the indicator restricts it to |y|<1; min(1,y^2) is bounded below by min(1,r^2) on the far-jump set. This supplies uniform-in-x domination needed for the compact-localized Levy generator Fubini argument.
-- source:
--   Uniform version of the accepted away-zero generator estimate in the analytic proof of Avram, Palmowski and Pistorius (2007), Lemma 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_uniform_far_jump_bound_on_compact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u r : ℝ)
    (hl : 0 < l) (hlu : l < u) (hu : u < a) (hr : 0 < r)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Icc l u, ∀ y < 0, y ≤ -r →
        ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ ≤
          C * min 1 (y ^ 2) := by sorry

end AvramDividend.Classical
