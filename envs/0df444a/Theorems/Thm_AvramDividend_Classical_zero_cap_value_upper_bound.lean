-- Prove2me | Theorems.Thm_AvramDividend_Classical_zero_cap_value_upper_bound
-- name    : AvramDividend.Classical.zero_cap_value_upper_bound
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T17:50:22.985229+00:00
-- url     : https://prove2.me/theorems/c019e4fa-dabb-4cb6-a906-33f150f0a179
-- title:
--   The zero-barrier candidate dominates every strategy with reserve cap zero
-- statement:
--   If admissible controlled reserves are required to remain at or below zero, the zero barrier is the extremal feasible reflection policy. Starting above zero first forces the excess initial capital to be paid immediately, and starting at zero the controlled reserve cannot become positive before ruin. Consequently every zero-capped strategy is bounded by the value of the barrier strategy at zero, represented by barrierValue W 0.
-- source:
--   Zero-cap branch of Avram, Palmowski and Pistorius (2007), Theorem 2(i). Proposition 4(i) is stated only for C>0, so this source-faithful child isolates the degenerate C=0 verification argument required by the formal theorem statement.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

namespace AvramDividend.Classical

theorem zero_cap_value_upper_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing) (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W) :
    ∀ x : ℝ, 0 ≤ x →
      valueFunctionLe X q 0 x ≤ ENNReal.ofReal (barrierValue W 0 x) := by
  sorry

end AvramDividend.Classical
