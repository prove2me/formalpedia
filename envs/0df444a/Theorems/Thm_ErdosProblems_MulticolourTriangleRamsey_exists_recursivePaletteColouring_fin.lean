-- Prove2me | Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_exists_recursivePaletteColouring_fin
-- name    : ErdosProblems.MulticolourTriangleRamsey.exists_recursivePaletteColouring_fin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:17.142639+00:00
-- url     : https://prove2.me/theorems/4ba75519-c5ab-4d04-9abd-409175b8399d
-- title:
--   ErdosProblems.MulticolourTriangleRamsey.exists_recursivePaletteColouring_fin
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MulticolorTriangleRamsey | external Lean 4.33.1 validation; bundle SHA256 5e423a288537515dc44d408ae78404638fc8edef2d065a20614dd79cba62ea87

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology

theorem ErdosProblems.MulticolourTriangleRamsey.exists_recursivePaletteColouring_fin
    {n N t j H : ℕ}
    (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin (N - t)))
    (htriangle : ∀ colour : Fin (N - t),
      (C.labelGraph colour).CliqueFree 3)
    (hC : ∀ colour : Fin (N - t), (C.labelGraph colour).Colorable j)
    (hH : 2 ≤ H) (hj : j ≤ H)
    (family : Finset (Finset (Fin N)))
    (hcard : ∀ P ∈ family, P.card = t)
    (hseparated : IsPaletteSeparated (saturatedMatrixRows H) family) :
    ∃ C' : SimpleGraph.TopEdgeLabeling
        (Fin (family.card * n)) (Fin N),
      TriangleFree C' ∧
        (∀ colour : Fin N, (C'.labelGraph colour).Colorable (j + 1)) := by sorry
