-- Prove2me | Theorems.Thm_Erdos266_finSum_succ
-- name    : Erdos266.finSum_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:56:10.529027+00:00
-- url     : https://prove2.me/theorems/96f3cc96-e11e-4d87-8eb2-dc2d9b12bd3e
-- title:
--   Erdos266: fin Sum succ
-- statement:
--   The Erdos266 construction uses the fin Sum succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Recursion.lean#L57-L59
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Recursion.lean#L57-L59

module
public import Definitions.Def_Erdos266_Algorithm
public import Definitions.Def_Erdos266_Recursion
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.finSum_succ (i k : ℕ) (S : ℕ → ℕ → ℤ) :
    finSum i (k + 1) S = finSum i k S + ∑ j ∈ range (dOf k), f (i + 1) (elemR S k j) := by sorry
