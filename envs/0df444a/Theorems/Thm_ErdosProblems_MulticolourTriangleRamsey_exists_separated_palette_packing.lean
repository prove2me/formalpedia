-- Prove2me | Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_exists_separated_palette_packing
-- name    : ErdosProblems.MulticolourTriangleRamsey.exists_separated_palette_packing
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:17.142639+00:00
-- url     : https://prove2.me/theorems/fc06dfa3-0edc-443f-9f49-26db358d3158
-- title:
--   ErdosProblems.MulticolourTriangleRamsey.exists_separated_palette_packing
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MulticolorTriangleRamsey | external Lean 4.33.1 validation; bundle SHA256 5e423a288537515dc44d408ae78404638fc8edef2d065a20614dd79cba62ea87

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology

theorem ErdosProblems.MulticolourTriangleRamsey.exists_separated_palette_packing (N t s : ℕ) (hs : 0 < s) :
    ∃ family : Finset (Finset (Fin N)),
      family ⊆ (Finset.univ : Finset (Fin N)).powersetCard t ∧
      IsPaletteSeparated s family ∧
      N.choose t ≤ family.card *
        (∑ d ∈ Finset.range s, t.choose d * (N - t).choose d) := by sorry
