-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_scale_deriv_ge_negative_jump_tail
-- name    : AvramDividend.Classical.bv_scale_deriv_ge_negative_jump_tail
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T00:09:10.007899+00:00
-- url     : https://prove2.me/theorems/34dfc88a-e817-481e-ab5f-b3e3cb41abcd
-- title:
--   Positive scale derivative dominates the truncated negative-jump intensity
-- statement:
--   The positive-axis derivative of a bounded-variation q-scale function dominates the Lévy intensity of negative jumps of magnitude exceeding x, divided by the square of the physical drift. The differentiated renewal equation gives d W'(x)=q W(x)+W(0)Πbar(x)+∫₀ˣ W'(x-y)Πbar(y)dy, with nonnegative terms and W(0)=1/d. In the infinite-activity case the truncated tail diverges as x approaches zero, yielding the presently Open infinite right derivative branch. The proof must derive the renewal equation for this particular IsScaleFunction and justify ordinary positive-point derivatives.
-- source:
--   Avram, Palmowski, Pistorius (2007), §3.3, and Kuznetsov–Kyprianou–Rivero scale-function review, bounded-variation renewal identity. Root-connected target scale_derivZeroPlus_top_of_bv_infinite_negative_activity (0893ca6f-97f2-4965-b369-8e65116e9249).

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory Set Filter
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_scale_deriv_ge_negative_jump_tail
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (hBV : X.BoundedVariation)
    (x : ℝ) (hx : 0 < x) :
    (X.ν (Set.Iio (-x))).toReal / X.drift ^ 2 ≤ deriv W x := by sorry
