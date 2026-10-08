-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_smooth_below_positive_cstar
-- name    : AvramDividend.Classical.vcstar_smooth_below_positive_cstar
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T20:48:04.672976+00:00
-- url     : https://prove2.me/theorems/abc53032-95fc-4630-afb1-742ae38fc0db
-- title:
--   Smoothness of vcstar strictly below a positive finite c-star
-- statement:
--   Under the smoothness alternatives used in Theorem 2, vcstar has exactly the C2 regularity required by Proposition 4(i) in the unbounded-variation case and the C1 regularity required in the bounded-variation case, on the interval strictly below positive c*. The explicit C2 hypothesis handles the residual branch, while condition (3.3) supplies the standard scale-function regularity in the Gaussian and bounded-variation cases.
-- source:
--   Avram, Palmowski and Pistorius (2007), condition (3.3), Theorem 2 smoothness proviso and Proposition 4(i), pp. 5 and 14-18. Source-faithful regularity reduction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem vcstar_smooth_below_positive_cstar
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hc : cstar W < ⊤) (hcpos : 0 < cstar W)
    (h_smooth : 0 < X.σ ∨ X.BoundedVariation ∨ ContDiffOn ℝ 2 (vcstar W) (Ioi 0)) :
    (¬ X.BoundedVariation →
        ContDiffOn ℝ 2 (vcstar W)
          {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cstar W}) ∧
      (X.BoundedVariation →
        ContDiffOn ℝ 1 (vcstar W)
          {y : ℝ | 0 < y ∧ ENNReal.ofReal y < cstar W}) := by
  sorry

end AvramDividend.Classical
