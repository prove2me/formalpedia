-- Prove2me | Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_exists_stage_palette_packing_exp
-- name    : ErdosProblems.MulticolourTriangleRamsey.exists_stage_palette_packing_exp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:17.142639+00:00
-- url     : https://prove2.me/theorems/384dae9f-43b1-49d7-8e45-88219d8643d2
-- title:
--   ErdosProblems.MulticolourTriangleRamsey.exists_stage_palette_packing_exp
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MulticolorTriangleRamsey | external Lean 4.33.1 validation; bundle SHA256 5e423a288537515dc44d408ae78404638fc8edef2d065a20614dd79cba62ea87

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology

theorem ErdosProblems.MulticolourTriangleRamsey.exists_stage_palette_packing_exp (j a s : ℕ)
    (hj : 0 < j) (ha : 2 ≤ a) (hs : 0 < s) :
    ∃ family : Finset (Finset (Fin (j * (a * s)))),
      family ⊆
        (Finset.univ : Finset (Fin (j * (a * s)))).powersetCard (a * s) ∧
      IsPaletteSeparated s family ∧
      (j : ℝ) ^ (a * s) ≤
        (family.card : ℝ) * (s : ℝ) *
          (Real.exp 1 ^ 2 * (a : ℝ) ^ 2 * (j : ℝ)) ^ s := by sorry
