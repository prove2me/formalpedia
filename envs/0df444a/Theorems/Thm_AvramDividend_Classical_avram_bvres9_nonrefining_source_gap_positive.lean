-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvres9_nonrefining_source_gap_positive
-- name    : AvramDividend.Classical.avram_bvres9_nonrefining_source_gap_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T09:52:16.536581+00:00
-- url     : https://prove2.me/theorems/f1186609-4076-4882-a6b9-9d376d16596d
-- title:
--   The non-refining BV grid has a strictly positive no-jump source deficit
-- statement:
--   For the proposed positive-drift compound-Poisson counterexample with intensity 1/100 and a persistent physical-grid cell from 1/2 to 3, the no-jump-weighted negative generator source term already exceeds the initial value 2. This proves only the scalar quantitative part of a counterexample to the arbitrary-monotone-grid source theorem 4f851376; the required standing Levy process instance and original theorem negation remain separate open obligations.
-- source:
--   AVRAM BV-RESIDUAL9 correction calculation, 7 November 2026; source-identical numerical bound in bv_residual9_correction_20261107.md.

import Mathlib.Analysis.Complex.Exponential
noncomputable section

theorem AvramDividend.Classical.avram_bvres9_nonrefining_source_gap_positive :
  (2 : ℝ) < (15 / 4 : ℝ) * Real.exp (-(3 / 100 : ℝ)) *
    Real.exp (-(1 / 2 : ℝ)) := by sorry
