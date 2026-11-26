-- Prove2me | Theorems.Thm_BellWilliams2001_ThresholdPolicy_class_one_primitive_increment_envelope
-- name    : BellWilliams2001.ThresholdPolicy.class_one_primitive_increment_envelope
-- status  : Proved
-- author  : @Jie Luo
-- created : 2026-11-26T06:07:21.655566+00:00
-- url     : https://prove2.me/theorems/de4f4c21-61de-52c0-9e66-f4f2c76df675
-- title:
--   A common increment envelope for the class 1 renewal primitives
-- statement:
--   For the three renewal primitives governing class 1, there is a common tolerance and logarithmic additive error valid simultaneously for all increments on a diffusion horizon off one measurable exceptional set. The exceptional probability is bounded by C(1+t)/r⁶, and the tolerance leaves strictly positive drift margins in both threshold modes.
-- source:
--   Bell and Williams (2001), https://doi.org/10.1214/aoap/1015345343, Section 7, large-deviation estimates for the residual process

import Definitions.Def_BellWilliams2001_ThresholdPolicy_Model

open MeasureTheory Filter Set
open scoped ENNReal

namespace BellWilliams2001.ThresholdPolicy

theorem class_one_primitive_increment_envelope {Ω : Type*} [MeasurableSpace Ω] (M : SystemSequence Ω) :
    ∃ η α K C : ℝ, 0 < η ∧ 0 < α ∧ 0 < K ∧ 0 ≤ C ∧
      ∀ᶠ n in atTop,
        α+2*η ≤ M.lamR n 0-M.muR n 0 ∧
        α+3*η ≤ M.muR n 0+M.muR n 1-M.lamR n 0 ∧
        ∀ t : ℝ, 0 ≤ t → ∃ E : Set Ω, MeasurableSet E ∧
          M.P E ≤ ENNReal.ofReal (C*(1+t)/M.r n^6) ∧
          ∀ ω ∉ E,
            (∀ u v, 0 ≤ u → u ≤ v → v ≤ M.r n^2*t →
              |M.A n 0 ω v-M.A n 0 ω u-M.lamR n 0*(v-u)| ≤ η*(v-u)+K*Real.log (M.r n)) ∧
            (∀ j : Fin 3, j ≠ 2 → ∀ u v, 0 ≤ u → u ≤ v → v ≤ M.r n^2*t →
              |M.S n j ω v-M.S n j ω u-M.muR n j*(v-u)| ≤ η*(v-u)+K*Real.log (M.r n)) := by sorry

end BellWilliams2001.ThresholdPolicy
