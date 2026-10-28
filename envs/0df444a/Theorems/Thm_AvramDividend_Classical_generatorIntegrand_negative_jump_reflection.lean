-- Prove2me | Theorems.Thm_AvramDividend_Classical_generatorIntegrand_negative_jump_reflection
-- name    : AvramDividend.Classical.generatorIntegrand_negative_jump_reflection
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:26:58.049012+00:00
-- url     : https://prove2.me/theorems/87cd84ae-9c51-4160-8a0f-35e51161d059
-- title:
--   Compensated generator jump integrand is reflected positive-magnitude kernel
-- statement:
--   For every negative Lévy jump y, substitute the positive jump magnitude z=−y. The positive-magnitude compensated kernel W(x−z)−W(x)+(if z<1 then zW′(x) else 0) equals the canonical signed generator integrand W(x+y)−W(x)−yW′(x)1_{(-1,1)}(y). The indicator and threshold agree in both near- and far-jump cases.
-- source:
--   Avram, Palmowski and Pistorius (2007), Lévy generator in Lemma 4; exact negative-jump substitution.

import Mathlib.Algebra.Order.Ring.Defs
import Mathlib.Analysis.Calculus.Deriv.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set

namespace AvramDividend.Classical

theorem generatorIntegrand_negative_jump_reflection
    (W : ℝ → ℝ) (x y : ℝ) (hy : y < 0) :
    W (x - (-y)) - W x +
      (if -y < 1 then (-y) * deriv W x else 0) =
    SpectrallyNegativeLevy.generatorIntegrand W x y := by sorry

end AvramDividend.Classical
