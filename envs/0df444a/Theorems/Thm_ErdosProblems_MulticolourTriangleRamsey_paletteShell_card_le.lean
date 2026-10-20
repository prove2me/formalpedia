-- Prove2me | Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_paletteShell_card_le
-- name    : ErdosProblems.MulticolourTriangleRamsey.paletteShell_card_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:17.142639+00:00
-- url     : https://prove2.me/theorems/bf158f2c-9f6b-4215-aafa-cc0baa05bbdc
-- title:
--   ErdosProblems.MulticolourTriangleRamsey.paletteShell_card_le
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MulticolorTriangleRamsey | external Lean 4.33.1 validation; bundle SHA256 5e423a288537515dc44d408ae78404638fc8edef2d065a20614dd79cba62ea87

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology

theorem ErdosProblems.MulticolourTriangleRamsey.paletteShell_card_le (N t d : ℕ)
    (Q : Finset (Fin N)) (hQ : Q.card = t) :
    (paletteShell N t Q d).card ≤
      t.choose d * (N - t).choose d := by sorry
