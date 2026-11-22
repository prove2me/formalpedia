-- Prove2me | Theorems.Thm_Digraph_mem_edgeFinset
-- name    : Digraph.mem_edgeFinset
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T10:09:00.231811+00:00
-- url     : https://prove2.me/theorems/b88abcc3-2c23-4bee-8ad6-e3f5e954a42f
-- title:
--   Digraph: mem edge Finset
-- statement:
--   The Digraph construction uses the mem edge Finset property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Digraph/Defs.lean#L54-L56
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/CircuitComplexity/Digraph/Defs.lean#L54-L56

module
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Data.Fintype.Prod
public import Mathlib.Order.Lattice.Nat
public import Definitions.Def_LeanPool_CircuitComplexity_Digraph_Defs
set_option autoImplicit true
@[expose] public section
public section
open Digraph
variable {V : Type*}

theorem Digraph.mem_edgeFinset [Fintype V] [DecidableEq V] {G : Digraph V}
    [DecidableRel G.Adj] {e : V × V} : e ∈ G.edgeFinset ↔ G.Adj e.1 e.2 := by sorry
