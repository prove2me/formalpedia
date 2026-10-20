-- Prove2me | Theorems.Thm_ErdosProblems_MulticolourTriangleRamsey_labelGraph_pullback_embedding
-- name    : ErdosProblems.MulticolourTriangleRamsey.labelGraph_pullback_embedding
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-19T10:56:15.843669+00:00
-- url     : https://prove2.me/theorems/28635eba-a052-4f42-92a5-d505320882c9
-- title:
--   ErdosProblems.MulticolourTriangleRamsey.labelGraph_pullback_embedding
-- source:
--   https://github.com/openai/ten-proofs/tree/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6 | MulticolorTriangleRamsey | external Lean 4.33.1 validation; bundle SHA256 5e423a288537515dc44d408ae78404638fc8edef2d065a20614dd79cba62ea87

import Mathlib
import Definitions.Def_MulticolorTriangleRamsey
set_option autoImplicit true
open ErdosProblems ErdosProblems.MulticolourTriangleRamsey
open Filter Finset SimpleGraph
open scoped Topology

theorem ErdosProblems.MulticolourTriangleRamsey.labelGraph_pullback_embedding {U V K : Type*}
    (C : SimpleGraph.TopEdgeLabeling V K)
    (f : U ↪ V) (colour : K) :
    (C.pullback f).labelGraph colour = (C.labelGraph colour).comap f := by sorry
