-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_local_verification_regular_of_positive_cstar
-- name    : AvramDividend.Classical.vcstar_local_verification_regular_of_positive_cstar
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T17:50:22.965434+00:00
-- url     : https://prove2.me/theorems/a697f73c-f07b-45f4-b758-d8bf6a649adc
-- title:
--   Regularity and boundary hypotheses for local verification at a positive finite c-star
-- statement:
--   When c* is positive and finite, the candidate v_{c*} has the continuity, nonnegative boundary value, zero extension to the negative half-line and the bounded-variation/unbounded-variation smoothness needed to invoke Proposition 4(i). The standing condition (3.3) supplies the automatic scale-function regularity in the Gaussian and bounded-variation branches; the remaining branch uses the explicit C2 hypothesis of Theorem 2.
-- source:
--   Avram, Palmowski and Pistorius (2007), condition (3.3), the scale-function regularity discussion before Theorem 2, and Proposition 4(i), pp. 5 and 14-18. Formal regularity package for applying local verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem vcstar_local_verification_regular_of_positive_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    ContinuousOn (vcstar W) (Ici 0) ∧
      0 ≤ vcstar W 0 ∧
      (∀ y < 0, vcstar W y = 0) ∧
      ((¬ X.BoundedVariation →
          ContDiffOn ℝ 2 (vcstar W)
            {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cstar W}) ∧
       (X.BoundedVariation →
          ContDiffOn ℝ 1 (vcstar W)
            {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cstar W})) := by
  sorry

end AvramDividend.Classical
