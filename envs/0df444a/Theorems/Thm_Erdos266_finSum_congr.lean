-- Prove2me | Theorems.Thm_Erdos266_finSum_congr
-- name    : Erdos266.finSum_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:56:19.069162+00:00
-- url     : https://prove2.me/theorems/1c4be2a3-6c4a-4947-a34d-df11dad9a6c1
-- title:
--   Erdos266: fin Sum congr
-- statement:
--   The Erdos266 construction uses the fin Sum congr property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Recursion.lean#L51-L55
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Recursion.lean#L51-L55

module
public import Definitions.Def_Erdos266_Algorithm
public import Definitions.Def_Erdos266_Recursion
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.finSum_congr {i k : ℕ} {S S' : ℕ → ℕ → ℤ}
    (h : ∀ l, l < k → ∀ j, j < dOf l → S l j = S' l j) :
    finSum i k S = finSum i k S' := by sorry
