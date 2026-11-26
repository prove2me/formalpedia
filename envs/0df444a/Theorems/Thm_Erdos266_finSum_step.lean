-- Prove2me | Theorems.Thm_Erdos266_finSum_step
-- name    : Erdos266.finSum_step
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:59:22.432596+00:00
-- url     : https://prove2.me/theorems/bfbc92ec-d663-5cf2-9b94-6927a08d0a5d
-- title:
--   Erdos266: fin Sum step
-- statement:
--   The new-block part of the updated partial sum is the lattice's shifted
--   sample sum.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Recursion.lean#L214-L224
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Recursion.lean#L214-L224

module
public import Definitions.Def_Erdos266_Algorithm
public import Definitions.Def_Erdos266_Recursion
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.finSum_step {k : ℕ} {st : AlgSt} (h : Inv k st) (i : ℕ) :
    finSum i (k + 1) (newS k st h)
      = finSum i k st.1 + ∑ j : Fin (dOf k),
          f (i + 1) ((((j.val + 1) * bigN k : ℕ) : ℝ) + (blk k st h j : ℝ)) := by sorry
