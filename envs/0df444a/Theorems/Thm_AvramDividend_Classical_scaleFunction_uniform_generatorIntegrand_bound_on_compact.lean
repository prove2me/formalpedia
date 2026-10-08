-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_uniform_generatorIntegrand_bound_on_compact
-- name    : AvramDividend.Classical.scaleFunction_uniform_generatorIntegrand_bound_on_compact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T22:35:15.98429+00:00
-- url     : https://prove2.me/theorems/9c9be0b1-6977-47d7-9d94-07f0025fa581
-- title:
--   Uniform Levy compensated-integrand domination on a compact state interval
-- statement:
--   Let W be a q-scale function that is C2 on (0,a). For any closed interval [l,u] with 0<l<u<a, there exists C>=0 such that for every x in that interval and every negative jump y the compensated generator integrand at (x,y) is bounded in norm by C min(1,y^2). The near-zero region follows from a uniform compact Taylor estimate with a radius r independent of x; the far-jump region follows from scale-function monotonicity and a uniform bound on the first derivative. Taking the maximum of both coefficients gives the global-in-jump domination uniform over the compact state set. This implies integrability against the Levy measure uniformly in x and is intended as the domination bridge for local Fubini and generator-harmonicity analysis.
-- source:
--   Compact-localized dominated Levy generator argument in the proof of Lemma 4 of Avram, Palmowski and Pistorius (2007).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_uniform_generatorIntegrand_bound_on_compact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u : ℝ)
    (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC2 : ContDiffOn ℝ 2 W (Ioo 0 a)) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Icc l u, ∀ y < 0,
        ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ ≤
          C * min 1 (y ^ 2) := by sorry

end AvramDividend.Classical
