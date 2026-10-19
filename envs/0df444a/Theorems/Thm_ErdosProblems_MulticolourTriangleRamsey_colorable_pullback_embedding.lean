-- Prove2me | Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_colorable_pullback_embedding
-- name    : ErdosProblems.MulticolourTriangleRamsey.colorable_pullback_embedding
-- status  : Open
-- author  : @marwahaha
-- created : 2026-10-19T10:56:15.843669+00:00
-- url     : https://prove2.me/theorems/14bfaa63-aa4a-4040-b000-8ad2645292dc
-- title:
--   ErdosProblems.MulticolourTriangleRamsey.colorable_pullback_embedding
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MulticolorTriangleRamsey | external Lean 4.33.1 validation; bundle SHA256 5e423a288537515dc44d408ae78404638fc8edef2d065a20614dd79cba62ea87

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology

theorem ErdosProblems.MulticolourTriangleRamsey.colorable_pullback_embedding {U V K : Type*} {j : ℕ}
    (C : SimpleGraph.TopEdgeLabeling V K)
    (f : U ↪ V) (colour : K)
    (hC : (C.labelGraph colour).Colorable j) :
    ((C.pullback f).labelGraph colour).Colorable j := by sorry
