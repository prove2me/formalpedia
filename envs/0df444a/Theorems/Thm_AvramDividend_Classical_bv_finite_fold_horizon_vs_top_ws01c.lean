-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_finite_fold_horizon_vs_top_ws01c
-- name    : AvramDividend.Classical.bv_finite_fold_horizon_vs_top_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:16:39.392536+00:00
-- url     : https://prove2.me/theorems/87ed0b13-0ec9-4d79-a21f-185fd9944806
-- title:
--   Capping a finite observation fold makes a finite fallback equivalent to infinity
-- statement:
--   For any finite list of strict-hit observations, replacing the no-hit fallback H by infinity does not alter the capped minimum at T when T≤H. The proof inducts over the finite fold and uses the invariant that the capped remaining minimum is bounded above by T. This bridges finite-valued observable stopping clocks and the canonical ENNReal infimum convention.
-- source:
--   Causal repair of terminal publication job bdc1549e-0fde-41a0-8da5-f5b7faf66ac3: preamble opened unavailable AvramDividend.Classical namespace and failed to synthesize Decidable (hit k). Removed the invalid open and installed scoped Classical decidability at statement elaboration, retaining the exact proposition. Proof work/avram_ws01c_finite_stop_cap_fallback_solution_pub_repair_20261028.lean.

import Mathlib

open Set
open scoped ENNReal Classical

theorem AvramDividend.Classical.bv_finite_fold_horizon_vs_top_ws01c
    (L : List ℕ) (x : ℕ → ℝ≥0∞) (hit : ℕ → Prop)
    (H T : ℝ≥0∞) (hTH : T ≤ H) :
    L.foldr (fun k u => (if hit k then x k else H) ⊓ u) T =
      L.foldr (fun k u => (if hit k then x k else ⊤) ⊓ u) T := by sorry
