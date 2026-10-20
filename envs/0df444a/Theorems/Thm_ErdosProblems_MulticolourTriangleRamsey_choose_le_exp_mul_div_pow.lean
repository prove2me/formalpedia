-- Prove2me | Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_choose_le_exp_mul_div_pow
-- name    : ErdosProblems.MulticolourTriangleRamsey.choose_le_exp_mul_div_pow
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:17.142639+00:00
-- url     : https://prove2.me/theorems/1b85e2ec-8ae3-4488-8f55-7e06c3f0be9b
-- title:
--   ErdosProblems.MulticolourTriangleRamsey.choose_le_exp_mul_div_pow
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MulticolorTriangleRamsey | external Lean 4.33.1 validation; bundle SHA256 5e423a288537515dc44d408ae78404638fc8edef2d065a20614dd79cba62ea87

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology

theorem ErdosProblems.MulticolourTriangleRamsey.choose_le_exp_mul_div_pow (N s : ℕ) (hs : 0 < s) :
    (N.choose s : ℝ) ≤
      (Real.exp 1 * (N : ℝ) / (s : ℝ)) ^ s := by sorry
