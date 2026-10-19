-- Prove2me | Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_quantitativeLowerBound_explicit_small
-- name    : ErdosProblems.MulticolourTriangleRamsey.quantitativeLowerBound_explicit_small
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:18.478977+00:00
-- url     : https://prove2.me/theorems/7c2b20dc-7ba8-45cf-8056-a3a0c5133ea2
-- title:
--   ErdosProblems.MulticolourTriangleRamsey.quantitativeLowerBound_explicit_small
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MulticolorTriangleRamsey | external Lean 4.33.1 validation; bundle SHA256 5e423a288537515dc44d408ae78404638fc8edef2d065a20614dd79cba62ea87

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology

theorem ErdosProblems.MulticolourTriangleRamsey.quantitativeLowerBound_explicit_small (k : ℕ)
    (hk : 2 ≤ k) (hsmall : k < 342) :
    (((1 : ℝ) / (6 * Real.exp 38)) *
      (k : ℝ) ^ ((1 : ℝ) / 3) / Real.log (k : ℝ)) ^ k ≤
        (triangleRamseyNumber k : ℝ) := by sorry
