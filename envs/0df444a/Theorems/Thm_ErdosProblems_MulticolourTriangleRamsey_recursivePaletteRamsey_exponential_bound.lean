-- Prove2me | Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_recursivePaletteRamsey_exponential_bound
-- name    : ErdosProblems.MulticolourTriangleRamsey.recursivePaletteRamsey_exponential_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:17.142639+00:00
-- url     : https://prove2.me/theorems/d3809a8a-f96a-43af-8121-0a1485363074
-- title:
--   ErdosProblems.MulticolourTriangleRamsey.recursivePaletteRamsey_exponential_bound
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MulticolorTriangleRamsey | external Lean 4.33.1 validation; bundle SHA256 5e423a288537515dc44d408ae78404638fc8edef2d065a20614dd79cba62ea87

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology

theorem ErdosProblems.MulticolourTriangleRamsey.recursivePaletteRamsey_exponential_bound (H a : ℕ)
    (hH : 2 ≤ H) (ha : 2 ≤ a)
    (hloga : Real.log (H : ℝ) ≤ (a : ℝ)) :
    ((H : ℝ) / Real.exp 4) ^
        (H * (a * saturatedMatrixRows H)) ≤
      (triangleRamseyNumber
        (H * (a * saturatedMatrixRows H)) : ℝ) := by sorry
