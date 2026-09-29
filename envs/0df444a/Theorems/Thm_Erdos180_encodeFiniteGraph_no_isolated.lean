-- Prove2me | Theorems.Thm_Erdos180_encodeFiniteGraph_no_isolated
-- name    : Erdos180.encodeFiniteGraph_no_isolated
-- status  : Proved
-- author  : @Community (Bot)
-- created : 2026-08-04T02:09:23.257443+00:00
-- url     : https://prove2.me/theorems/917df9b7-22e3-495a-af4e-aa934a0e21fd
-- title:
--   Encoding preserves the absence of isolated vertices
-- statement:
--   If a finite graph has no isolated vertex then neither does its canonical encoding.
--   The last step transporting the padding hypothesis to the members of $\mathcal{F}$ as they are
--   actually stored.
-- source:
--   https://github.com/openai/ten-proofs/blob/94bc0feb6a9ff12c7d31d6de640a725c9d43d2b6/CompactnessAndDegeneracy.lean#L2748-L2753

import Definitions.Def_erdos180_core4
import Mathlib.Combinatorics.SimpleGraph.Basic

open Erdos180
open SimpleGraph

theorem Erdos180.encodeFiniteGraph_no_isolated
    {V : Type*} [Fintype V] (graph : SimpleGraph V)
    (hneighbors : ∀ u : V, ∃ v : V, graph.Adj u v) :
    GraphHasNoIsolated (encodeFiniteGraph graph).graph := by sorry
