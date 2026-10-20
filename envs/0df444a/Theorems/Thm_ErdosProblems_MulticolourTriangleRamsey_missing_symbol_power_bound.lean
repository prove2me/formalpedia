-- Prove2me | Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_missing_symbol_power_bound
-- name    : ErdosProblems.MulticolourTriangleRamsey.missing_symbol_power_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:17.142639+00:00
-- url     : https://prove2.me/theorems/9a190fd4-3926-4081-ac8a-d956f5410ca9
-- title:
--   ErdosProblems.MulticolourTriangleRamsey.missing_symbol_power_bound
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MulticolorTriangleRamsey | external Lean 4.33.1 validation; bundle SHA256 5e423a288537515dc44d408ae78404638fc8edef2d065a20614dd79cba62ea87

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology

theorem ErdosProblems.MulticolourTriangleRamsey.missing_symbol_power_bound (H m : ℕ) (hH : 2 ≤ H)
    (hm : 2 * (H : ℝ) * Real.log (H : ℝ) ≤ (m : ℝ)) :
    (H : ℝ) ^ 2 * ((H : ℝ) - 1) ^ (m + 1) <
      (H : ℝ) ^ (m + 1) := by sorry
