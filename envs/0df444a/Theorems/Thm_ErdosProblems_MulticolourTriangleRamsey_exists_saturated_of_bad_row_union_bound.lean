-- Prove2me | Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_exists_saturated_of_bad_row_union_bound
-- name    : ErdosProblems.MulticolourTriangleRamsey.exists_saturated_of_bad_row_union_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:17.142639+00:00
-- url     : https://prove2.me/theorems/2d6a5b86-0d25-4da9-80b6-7424654d2dbc
-- title:
--   ErdosProblems.MulticolourTriangleRamsey.exists_saturated_of_bad_row_union_bound
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MulticolorTriangleRamsey | external Lean 4.33.1 validation; bundle SHA256 5e423a288537515dc44d408ae78404638fc8edef2d065a20614dd79cba62ea87

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology

theorem ErdosProblems.MulticolourTriangleRamsey.exists_saturated_of_bad_row_union_bound (H m s : ℕ)
    (hbound :
      (∑ T ∈
          (Finset.univ : Finset (Fin m → Fin H)).powersetCard (m + 1),
        (badSaturationRows H m T).card ^ s) <
          Fintype.card (Fin s → (Fin m → Fin H) → Fin H)) :
    ∃ A : Fin s → (Fin m → Fin H) → Fin H, IsSaturated A := by sorry
