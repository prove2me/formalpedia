-- Prove2me | Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_choose_le_choose_of_le_half
-- name    : ErdosProblems.MulticolourTriangleRamsey.choose_le_choose_of_le_half
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:17.142639+00:00
-- url     : https://prove2.me/theorems/1c294b78-4c40-49b4-9f67-3a5bfbe4e0c1
-- title:
--   ErdosProblems.MulticolourTriangleRamsey.choose_le_choose_of_le_half
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MulticolorTriangleRamsey | external Lean 4.33.1 validation; bundle SHA256 5e423a288537515dc44d408ae78404638fc8edef2d065a20614dd79cba62ea87

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology

theorem ErdosProblems.MulticolourTriangleRamsey.choose_le_choose_of_le_half {N d s : ℕ}
    (hds : d ≤ s) (hhalf : 2 * s ≤ N) :
    N.choose d ≤ N.choose s := by sorry
