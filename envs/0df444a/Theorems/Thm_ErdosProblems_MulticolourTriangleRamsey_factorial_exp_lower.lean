-- Prove2me | Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_factorial_exp_lower
-- name    : ErdosProblems.MulticolourTriangleRamsey.factorial_exp_lower
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:17.142639+00:00
-- url     : https://prove2.me/theorems/afc90da5-bbcc-4f25-8abe-dc1631e0bee6
-- title:
--   ErdosProblems.MulticolourTriangleRamsey.factorial_exp_lower
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MulticolorTriangleRamsey | external Lean 4.33.1 validation; bundle SHA256 5e423a288537515dc44d408ae78404638fc8edef2d065a20614dd79cba62ea87

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology

theorem ErdosProblems.MulticolourTriangleRamsey.factorial_exp_lower (s : ℕ) (hs : 0 < s) :
    ((s : ℝ) / Real.exp 1) ^ s ≤ (s.factorial : ℝ) := by sorry
