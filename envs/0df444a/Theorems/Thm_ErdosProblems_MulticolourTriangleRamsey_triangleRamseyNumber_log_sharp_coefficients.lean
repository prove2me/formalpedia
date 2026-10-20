-- Prove2me | Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_triangleRamseyNumber_log_sharp_coefficients
-- name    : ErdosProblems.MulticolourTriangleRamsey.triangleRamseyNumber_log_sharp_coefficients
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:18.478977+00:00
-- url     : https://prove2.me/theorems/cf4f65f2-a239-4877-ae36-b4620f14e73a
-- title:
--   ErdosProblems.MulticolourTriangleRamsey.triangleRamseyNumber_log_sharp_coefficients
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MulticolorTriangleRamsey | external Lean 4.33.1 validation; bundle SHA256 5e423a288537515dc44d408ae78404638fc8edef2d065a20614dd79cba62ea87

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology

theorem ErdosProblems.MulticolourTriangleRamsey.triangleRamseyNumber_log_sharp_coefficients :
    ∀ ε : ℝ, 0 < ε →
      ∀ᶠ k : ℕ in atTop,
        ((1 / 3 : ℝ) - ε) * (k : ℝ) * Real.log (k : ℝ) ≤
            Real.log (triangleRamseyNumber k : ℝ) ∧
          Real.log (triangleRamseyNumber k : ℝ) ≤
            (1 + ε) * (k : ℝ) * Real.log (k : ℝ) := by sorry
