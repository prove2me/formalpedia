-- Prove2me | Theorems.Thm_DenseTriangleFree_succ_mod_cases
-- name    : DenseTriangleFree.succ_mod_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:53:33.213871+00:00
-- url     : https://prove2.me/theorems/b0e37d50-e573-51cf-9e0a-254550932098
-- title:
--   Dense Triangle Free: succ mod cases
-- statement:
--   The Dense Triangle Free construction uses the succ mod cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Bipartite.lean#L32-L39
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Bipartite.lean#L32-L39

module
public import Mathlib
public import Definitions.Def_JinLib_KeyLemma
public import Definitions.Def_JinLib_Bipartite
set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph
variable {V : Type*} {G : SimpleGraph V}

theorem DenseTriangleFree.succ_mod_cases (i L : ℕ) (hL : 0 < L) :
    (i % L + 1 < L ∧ (i + 1) % L = i % L + 1) ∨ (i % L + 1 = L ∧ (i + 1) % L = 0) := by sorry
