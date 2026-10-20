-- Prove2me | Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_mem_missingSymbolRows
-- name    : ErdosProblems.MulticolourTriangleRamsey.mem_missingSymbolRows
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:17.142639+00:00
-- url     : https://prove2.me/theorems/7973cd54-e9c7-485a-950f-174827db50b4
-- title:
--   ErdosProblems.MulticolourTriangleRamsey.mem_missingSymbolRows
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MulticolorTriangleRamsey | external Lean 4.33.1 validation; bundle SHA256 5e423a288537515dc44d408ae78404638fc8edef2d065a20614dd79cba62ea87

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology

theorem ErdosProblems.MulticolourTriangleRamsey.mem_missingSymbolRows (H m : ℕ)
    (T : Finset (Fin m → Fin H)) (symbol : Fin H)
    (row : (Fin m → Fin H) → Fin H) :
    row ∈ missingSymbolRows H m T symbol ↔
      ∀ column ∈ T, row column ≠ symbol := by sorry
