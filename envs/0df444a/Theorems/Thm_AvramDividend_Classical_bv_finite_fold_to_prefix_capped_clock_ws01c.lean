-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_finite_fold_to_prefix_capped_clock_ws01c
-- name    : AvramDividend.Classical.bv_finite_fold_to_prefix_capped_clock_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:47:34.43975+00:00
-- url     : https://prove2.me/theorems/54fb9f57-83b1-4d52-bb0f-0a04548275b7
-- title:
--   The capped finite observation fold equals the finite-prefix strict lower grid infimum
-- statement:
--   A finite first-hit observation fold with fallback H, capped at T≤H, equals the finite-prefix ENNReal infimum with a top fallback. This is an exact algebraic bridge from finite stopping clocks to the canonical all-grid right limit, using the Proved foldr/iInf and finite-horizon/top equivalences.
-- source:
--   Exact existing source work/avram_ws01c_finite_fold_to_prefix_cap_draft.lean. The formal signature and proof calculation are retained; imports now use canonically Proved helpers bv_foldr_min_eq_finite_iInf_ws01c UUID 2ce8bfa7-fbc8-4250-b464-0964b97febf1 and bv_finite_fold_horizon_vs_top_ws01c UUID 87ed0b13-0ec9-4d79-a21f-185fd9944806. Scoped Classical supplies decidable arbitrary hit propositions. Complete proof work/avram_ws01c_finite_fold_prefix_cap_solution_20261028.lean. The original research draft omitted one closing parenthesis around the left-hand capped fold; the new source/statement close it, without changing the mathematical equality.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_bv_foldr_min_eq_finite_iInf_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_finite_fold_horizon_vs_top_ws01c

open Set AvramDividend.Classical
open scoped ENNReal Classical

theorem AvramDividend.Classical.bv_finite_fold_to_prefix_capped_clock_ws01c
    (M : ℕ) (x : ℕ → ℝ≥0∞) (hit : ℕ → Prop)
    (H T : ℝ≥0∞) (hTH : T ≤ H) :
    (((List.range (M + 1)).foldr
        (fun k u => (if hit k then x k else H) ⊓ u) H) ⊓ T) =
      ((⨅ (k : ℕ) (_ : k ≤ M),
          if hit k then x k else ⊤) ⊓ T) := by sorry
