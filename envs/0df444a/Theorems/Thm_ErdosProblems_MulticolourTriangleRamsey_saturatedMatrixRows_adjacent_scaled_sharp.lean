-- Prove2me | Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_saturatedMatrixRows_adjacent_scaled_sharp
-- name    : ErdosProblems.MulticolourTriangleRamsey.saturatedMatrixRows_adjacent_scaled_sharp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:17.142639+00:00
-- url     : https://prove2.me/theorems/00bcf111-af80-464e-bff4-0f37f966f049
-- title:
--   ErdosProblems.MulticolourTriangleRamsey.saturatedMatrixRows_adjacent_scaled_sharp
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MulticolorTriangleRamsey | external Lean 4.33.1 validation; bundle SHA256 5e423a288537515dc44d408ae78404638fc8edef2d065a20614dd79cba62ea87

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology

theorem ErdosProblems.MulticolourTriangleRamsey.saturatedMatrixRows_adjacent_scaled_sharp (H : ℕ) (hH : 3 ≤ H) :
    H * saturatedMatrixRows (H + 1) ≤
      (H + 14) * saturatedMatrixRows H := by sorry
