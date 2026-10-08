-- Prove2me | Theorems.Thm_AvramDividend_Classical_cstar_optimal_barrier_of_right_deriv_gap
-- name    : AvramDividend.Classical.cstar_optimal_barrier_of_right_deriv_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T16:35:33.348383+00:00
-- url     : https://prove2.me/theorems/5c5aefdd-01c6-498b-9464-9140fc878796
-- title:
--   Optimal Avram dividend barrier under a strict one-sided derivative gap and positive derivative
-- statement:
--   For a canonical q-scale function whose derivative is continuous on the strictly positive half-line, assume a positive global derivative minimiser a and that its derivative lies strictly below the extended right-hand derivative at zero. With interior differentiability and strict positivity of the derivative at the resulting cstar level, prove the barrier cstar dominates every competing barrier for x in [0,cstar]. Unlike earlier conditional results, no artificial strict improvement relative to the ordinary derivative at zero and no explicit zero-boundary denominator comparison are needed. The latter is deduced from the strict right-liminf gap in EReal.
-- source:
--   Use the positive minimiser attainment helper based on the strict comparison with derivZeroPlus. Global derivative-minimality identifies the derivative at cstar with its value at a. The EReal strict boundary inequality implies a weak extended-derivative bound, and Mathlib EReal.toReal_le_toReal yields the real denominator comparison unless derivZeroPlus is top, in which case the infinity branch applies. The canonical IsScaleFunction yields nonnegativity and interval continuity of W. Apply the already Proved attained-positive-minimum barrier comparison.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

namespace AvramDividend.Classical

theorem cstar_optimal_barrier_of_right_deriv_gap
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : a ∈ cstarSet W)
    (hgap : ((deriv W a : ℝ) : EReal) < derivZeroPlus W)
    (hcontDeriv : ContinuousOn (deriv W) (Set.Ioi (0 : ℝ)))
    (hpositive : 0 < deriv W (cstar W).toReal)
    (hdiff : DifferentiableOn ℝ W (Set.Ioo 0 (cstar W).toReal)) :
    cstar W < ⊤ ∧
      ∀ x b : ℝ, 0 ≤ x → x ≤ (cstar W).toReal → 0 ≤ b →
        barrierValue W b x ≤ vcstar W x := by
  sorry

end AvramDividend.Classical
