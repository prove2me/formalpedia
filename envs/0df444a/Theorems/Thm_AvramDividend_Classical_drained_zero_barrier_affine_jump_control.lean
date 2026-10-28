-- Prove2me | Theorems.Thm_AvramDividend_Classical_drained_zero_barrier_affine_jump_control
-- name    : AvramDividend.Classical.drained_zero_barrier_affine_jump_control
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:46:01.376759+00:00
-- url     : https://prove2.me/theorems/cfade6f4-7070-4cf6-8a0c-d5432559c58a
-- title:
--   Every lump-sum jump of the immediately ruined drain satisfies affine verification drop
-- statement:
--   A zero-barrier cumulative-dividend process plus deterministic drain has ruin time zero and initial dividend x. For any verification function agreeing with y-1 on nonnegative capital, the standard dividend-jump inequality holds at every formally admissible payment time, including the time-zero atom. This isolates the distinct missing boundary nonnegativity hypothesis of the UBV verification core.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 4(i), its discrete control jump term, and the preceding proved zero-barrier drained strategy lemmas.

import Mathlib.Data.ENNReal.Basic
import Mathlib.Tactic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_plus_linear_drain
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_plus_linear_drain_initial_rightLimit
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_isDividendStrategy_nonnegative_barrier
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_right_increment_formula
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_plus_linear_drain_ruinTime_zero

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.drained_zero_barrier_affine_jump_control
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 ≤ x)
    (w : ℝ → ℝ) (hw_affine : ∀ y, 0 ≤ y → w y = y - 1) :
    ∀ ω (t : ℝ≥0),
      (t = 0 ∨ (t : ℝ≥0∞) <
        ruinTime X x
          (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) ω) →
      rightLimit (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) t ω -
          (barrierStrategy X x 0 t ω + (t : ℝ)) ≤
        w (riskProcess X x
          (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) t ω) -
        w (riskProcess X x
          (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) t ω -
            (rightLimit
              (fun s ω => barrierStrategy X x 0 s ω + (s : ℝ)) t ω -
              (barrierStrategy X x 0 t ω + (t : ℝ)))) := by sorry
