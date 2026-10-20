-- Prove2me | Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_exists_stage_palette_packing_binomial
-- name    : ErdosProblems.MulticolourTriangleRamsey.exists_stage_palette_packing_binomial
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:17.142639+00:00
-- url     : https://prove2.me/theorems/e234875c-15e6-4ce0-b100-29c2456e82a3
-- title:
--   ErdosProblems.MulticolourTriangleRamsey.exists_stage_palette_packing_binomial
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MulticolorTriangleRamsey | external Lean 4.33.1 validation; bundle SHA256 5e423a288537515dc44d408ae78404638fc8edef2d065a20614dd79cba62ea87

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology

theorem ErdosProblems.MulticolourTriangleRamsey.exists_stage_palette_packing_binomial (j t s : ℕ)
    (hs : 0 < s) (hj : 0 < j) (hhalf : 2 * s ≤ t) :
    ∃ family : Finset (Finset (Fin (j * t))),
      family ⊆ (Finset.univ : Finset (Fin (j * t))).powersetCard t ∧
      IsPaletteSeparated s family ∧
      j ^ t ≤ family.card *
        (s * t.choose s * (j * t).choose s) := by sorry
