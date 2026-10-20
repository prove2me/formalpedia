-- Prove2me | Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_triangleFree_deleteUnusedColour
-- name    : ErdosProblems.MulticolourTriangleRamsey.triangleFree_deleteUnusedColour
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:15.843669+00:00
-- url     : https://prove2.me/theorems/d0a76f85-23c1-4de4-a408-e10223392955
-- title:
--   ErdosProblems.MulticolourTriangleRamsey.triangleFree_deleteUnusedColour
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MulticolorTriangleRamsey | external Lean 4.33.1 validation; bundle SHA256 5e423a288537515dc44d408ae78404638fc8edef2d065a20614dd79cba62ea87

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology

theorem ErdosProblems.MulticolourTriangleRamsey.triangleFree_deleteUnusedColour {n k : ℕ}
    (C : SimpleGraph.TopEdgeLabeling (Fin n) (Fin (k + 1)))
    (omitted : Fin (k + 1))
    (hunused : ∀ edge : (⊤ : SimpleGraph (Fin n)).edgeSet,
      C edge ≠ omitted)
    (hC : TriangleFree C) :
    TriangleFree (deleteUnusedColour C omitted hunused) := by sorry
