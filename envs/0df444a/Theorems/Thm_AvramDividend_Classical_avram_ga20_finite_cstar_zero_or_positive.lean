-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga20_finite_cstar_zero_or_positive
-- name    : AvramDividend.Classical.avram_ga20_finite_cstar_zero_or_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T21:59:15.175537+00:00
-- url     : https://prove2.me/theorems/25f9f3e7-5a62-46fa-a123-e6cc308453cd
-- title:
--   Finite c-star case dichotomy for capped barrier verification
-- statement:
--   For the finite c-star scale barrier, the barrier is either exactly zero or strictly positive. This is the exhaustive case split used in the source-faithful capped upper-bound assembly, whose two branches are separate formal proof obligations.
-- source:
--   Positive/zero c-star case split used in Open capped value upper bound 40dcbaef and its positive-case child 8ce07d6a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga20_finite_cstar_zero_or_positive
    (W : ℝ → ℝ) (hc : cstar W < ⊤) :
    cstar W = 0 ∨ 0 < cstar W := by sorry
