-- Prove2me | Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_triangleRamseyNumber_log_eventually_bounds
-- name    : ErdosProblems.MulticolourTriangleRamsey.triangleRamseyNumber_log_eventually_bounds
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:18.478977+00:00
-- url     : https://prove2.me/theorems/31a45b31-2e19-4079-ba12-21776648f27d
-- title:
--   ErdosProblems.MulticolourTriangleRamsey.triangleRamseyNumber_log_eventually_bounds
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MulticolorTriangleRamsey | external Lean 4.33.1 validation; bundle SHA256 5e423a288537515dc44d408ae78404638fc8edef2d065a20614dd79cba62ea87

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology

theorem ErdosProblems.MulticolourTriangleRamsey.triangleRamseyNumber_log_eventually_bounds :
    ∀ᶠ k : ℕ in atTop,
      (1 / 6 : ℝ) * (k : ℝ) * Real.log (k : ℝ) ≤
          Real.log (triangleRamseyNumber k : ℝ) ∧
        Real.log (triangleRamseyNumber k : ℝ) ≤
          2 * (k : ℝ) * Real.log (k : ℝ) := by sorry
