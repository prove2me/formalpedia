-- Prove2me | Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_triangleRamseyNumber_factorial_upper
-- name    : ErdosProblems.MulticolourTriangleRamsey.triangleRamseyNumber_factorial_upper
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:15.843669+00:00
-- url     : https://prove2.me/theorems/e0d9290a-828f-476a-9873-e7d823aed4b6
-- title:
--   ErdosProblems.MulticolourTriangleRamsey.triangleRamseyNumber_factorial_upper
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MulticolorTriangleRamsey | external Lean 4.33.1 validation; bundle SHA256 5e423a288537515dc44d408ae78404638fc8edef2d065a20614dd79cba62ea87

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology

theorem ErdosProblems.MulticolourTriangleRamsey.triangleRamseyNumber_factorial_upper (k : ℕ) :
    triangleRamseyNumber k ≤ 4 * k.factorial := by sorry
