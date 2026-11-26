-- Prove2me | Theorems.Thm_Erdos266_term_nonneg
-- name    : Erdos266.term_nonneg
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T02:58:51.414085+00:00
-- url     : https://prove2.me/theorems/2cd991e5-09ab-41cd-bc15-5d3fa3d8f8bf
-- title:
--   Erdos266: term nonneg
-- statement:
--   The Erdos266 construction uses the term nonneg property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L456-L463
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Convergence.lean#L456-L463

module
public import Definitions.Def_Erdos266_Recursion
public import Definitions.Def_Erdos266_Reduction
public import Definitions.Def_Erdos266_Convergence
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset Filter Topology

theorem Erdos266.term_nonneg {i' m : ℕ} (hm : cnt (4 * i' + 4) ≤ m) :
    0 ≤ f (i' + 1) ((aSeq m : ℕ) : ℝ) := by sorry
