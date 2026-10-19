-- Prove2me | Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_palette_exp_loss_bound
-- name    : ErdosProblems.MulticolourTriangleRamsey.palette_exp_loss_bound
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:17.142639+00:00
-- url     : https://prove2.me/theorems/7e5c0ff5-bfbb-4623-9451-5ced25c405e1
-- title:
--   ErdosProblems.MulticolourTriangleRamsey.palette_exp_loss_bound
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MulticolorTriangleRamsey | external Lean 4.33.1 validation; bundle SHA256 5e423a288537515dc44d408ae78404638fc8edef2d065a20614dd79cba62ea87

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology

theorem ErdosProblems.MulticolourTriangleRamsey.palette_exp_loss_bound (H a s : ℕ)
    (hH : 2 ≤ H) (ha : 2 ≤ a) (hs : 0 < s)
    (hlogH : Real.log (H : ℝ) ≤ (a : ℝ)) :
    ((H : ℝ) / Real.exp 4) ^ (H * (a * s)) ≤
      ((H : ℝ) / Real.exp 1) ^ (H * ((a - 1) * s)) /
        ((s : ℝ) ^ H *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2) ^ (s * H)) := by sorry
