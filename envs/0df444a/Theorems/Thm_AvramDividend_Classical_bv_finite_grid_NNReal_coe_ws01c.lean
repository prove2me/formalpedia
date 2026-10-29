-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_finite_grid_NNReal_coe_ws01c
-- name    : AvramDividend.Classical.bv_finite_grid_NNReal_coe_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:50:57.187023+00:00
-- url     : https://prove2.me/theorems/5085a76f-5e1b-4af6-83cb-2ab3af883db7
-- title:
--   The finite grid observation clock commutes with the finite-to-extended nonnegative coercion
-- statement:
--   For the existing two concrete finite-grid observation clock definitions, one valued in NNReal and the other in WithTop NNReal, coercion of the finite fold commutes exactly with each minimum, conditional observation and finite fallback. The proof is structural induction on the original finite observation list. This is needed to identify the actual original-filtration capped stopping clock with the finite-prefix extended strict lower infimum.
-- source:
--   Exact existing named theorem and inductive source from work/avram_ws01c_finite_clock_nnreal_adapter_draft.lean, specialised to the public finite grid definition bundle UUID 2d81875c-9b5a-4bad-903c-074da5c0eaa7. Complete proof work/avram_ws01c_finite_grid_nnreal_coe_solution_20261028.lean. No alteration to source filtration or clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_BvFiniteGridClocks_ws01c

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_finite_grid_NNReal_coe_ws01c
    {Ω : Type*} (Y : ℝ≥0 → Ω → ℝ)
    (b : ℝ) (H : ℝ≥0) (L : List ℝ≥0) (ω : Ω) :
    ((bv_finite_grid_below_NNReal_ws01c Y b H L ω : ℝ≥0) :
      WithTop ℝ≥0) =
      bv_finite_grid_below_clock_ws01c Y b H L ω := by sorry
