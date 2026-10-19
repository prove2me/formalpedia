-- Prove2me | Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_allColourPaletteRamsey_exponential_bound_sharp
-- name    : ErdosProblems.MulticolourTriangleRamsey.allColourPaletteRamsey_exponential_bound_sharp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:17.142639+00:00
-- url     : https://prove2.me/theorems/acc9f53e-af92-496b-9ebb-239e296aeab2
-- title:
--   ErdosProblems.MulticolourTriangleRamsey.allColourPaletteRamsey_exponential_bound_sharp
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MulticolorTriangleRamsey | external Lean 4.33.1 validation; bundle SHA256 5e423a288537515dc44d408ae78404638fc8edef2d065a20614dd79cba62ea87

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology

theorem ErdosProblems.MulticolourTriangleRamsey.allColourPaletteRamsey_exponential_bound_sharp (k : ℕ)
    (hk : paletteColourCount 3 ≤ k) :
    ∃ H : ℕ,
      3 ≤ H ∧
      paletteColourCount H ≤ k ∧
      k < paletteColourCount (H + 1) ∧
      ((H : ℝ) / Real.exp 38) ^ k ≤
        (triangleRamseyNumber k : ℝ) := by sorry
