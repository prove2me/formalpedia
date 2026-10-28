-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_reciprocal_dyadic_mesh_cover_ws01c
-- name    : AvramDividend.Classical.bv_reciprocal_dyadic_mesh_cover_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:00:57.545033+00:00
-- url     : https://prove2.me/theorems/4941687a-d5c3-4308-b57f-3a97e1eddf95
-- title:
--   Every small positive nonnegative real lies between adjacent dyadic mesh points
-- statement:
--   For every N and every positive t smaller than the Nth reciprocal-dyadic mesh point in NNReal, there exists n≥N such that 2^(-n-1)≤t≤2^(-n). This supplies the exact covering hypothesis required by the already Proved deterministic monotone slope-to-right-germ theorem. It follows from dyadic antitonicity and the public Proved real dyadic scale selection theorem, with explicit NNReal coercions.
-- source:
--   Deterministic dyadic bracketing, reusing Proved LevyStochCalc.Brownian.Continuity.exists_dyadic_scale_readable (1d383b87-9bce-4bea-947b-c6594626f115). Consolidates work/avram_ws01c_dyadic_mesh_basic_draft.lean, work/avram_ws01c_dyadic_local_bracketing_draft.lean and work/avram_ws01c_exact_dyadic_cover_from_proved_scale_draft.lean into one source-faithful helper.

import Mathlib
import Theorems.Thm_LevyStochCalc_Brownian_Continuity_exists_dyadic_scale_readable

open Filter
open scoped NNReal

theorem AvramDividend.Classical.bv_reciprocal_dyadic_mesh_cover_ws01c
    (N : ℕ) (t : ℝ≥0)
    (ht : 0 < t) (htN : t < ((1 : ℝ≥0) / 2) ^ N) :
    ∃ n : ℕ,
      N ≤ n ∧ ((1 : ℝ≥0) / 2) ^ (n + 1) ≤ t ∧
      t ≤ ((1 : ℝ≥0) / 2) ^ n := by sorry
