-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_uniform_near_zero_bound_on_compact
-- name    : AvramDividend.Classical.scaleFunction_uniform_near_zero_bound_on_compact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:35:09.826478+00:00
-- url     : https://prove2.me/theorems/df9f9ec7-de02-41f0-a766-9fe2555251d8
-- title:
--   Uniform quadratic Taylor bound for small negative jumps on a compact starting-state interval
-- statement:
--   Let W be a q-scale function C2 on (0,a), and fix a compact [l,u] strictly inside (0,a). Then there is a single radius r>0, r<=min(l,1), and a single C>=0, such that for every x in [l,u] and jump -r<y<0, the norm of the compensated Levy-generator increment W(x+y)-W(x)-W'(x)y is at most C y^2. Choose r=min(l,1)/2 and K=[l-r,u] compactly contained in (0,a). Bound W'' uniformly on K by the extreme-value theorem and apply the Lagrange Taylor remainder uniformly to each segment [x+y,x]. This is the local uniform small-jump domination needed before interchanging the x integral and the Levy measure integral.
-- source:
--   Uniform-in-starting-state form of the accepted quadratic remainder lemma in the analytic proof of Avram, Palmowski and Pistorius (2007), Lemma 4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_uniform_near_zero_bound_on_compact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u : ℝ)
    (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ∃ r C : ℝ, 0 < r ∧ r ≤ min l 1 ∧ 0 ≤ C ∧
      ∀ x ∈ Icc l u, ∀ y ∈ Ioo (-r) 0,
        ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ ≤
          C * y ^ 2 := by sorry

end AvramDividend.Classical
