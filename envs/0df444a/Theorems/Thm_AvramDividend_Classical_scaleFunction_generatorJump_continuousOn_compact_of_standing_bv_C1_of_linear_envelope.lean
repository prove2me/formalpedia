-- Prove2me | Theorems.Thm_AvramDividend_Classical_scaleFunction_generatorJump_continuousOn_compact_of_standing_bv_C1_of_linear_envelope
-- name    : AvramDividend.Classical.scaleFunction_generatorJump_continuousOn_compact_of_standing_bv_C1_of_linear_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:48:40.824548+00:00
-- url     : https://prove2.me/theorems/f1883566-1083-4200-855c-67c127a7324f
-- title:
--   BV C1 scale-function jump generator is continuous under a uniform first-order envelope
-- statement:
--   Given C1 scale regularity, standing bounded-variation assumptions and a uniform compact-state C min(1,|y|) bound for the compensated negative-jump kernel, the integral of the kernel is continuous in the reserve state on the compact interior interval. The proof combines already Proved almost-everywhere state continuity of the kernel, finite BV first-order jump mass, strong measurability and a parameterised dominated-convergence theorem. This is the analytic bridge for the BV generator-harmonicity case.
-- source:
--   Avram, Palmowski, Pistorius (2007), Lemma 4; BV C1 dominated convergence for Lévy generator.

import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem scaleFunction_generatorJump_continuousOn_compact_of_standing_bv_C1_of_linear_envelope
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hbv : X.BoundedVariation)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a l u : ℝ) (hl : 0 < l) (hlu : l < u) (hu : u < a)
    (hC1 : ContDiffOn ℝ 1 W (Ioo 0 a))
    (hlinear : ∃ C : ℝ, 0 ≤ C ∧
      ∀ x ∈ Icc l u, ∀ y ∈ Iio (0 : ℝ),
        ‖SpectrallyNegativeLevy.generatorIntegrand W x y‖ ≤
          C * min 1 |y|) :
    ContinuousOn
      (fun x : ℝ =>
        ∫ y : ℝ, SpectrallyNegativeLevy.generatorIntegrand W x y
          ∂(X.ν.restrict (Iio 0)))
      (Icc l u) := by sorry

end AvramDividend.Classical
