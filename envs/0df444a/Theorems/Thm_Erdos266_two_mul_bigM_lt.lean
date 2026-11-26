-- Prove2me | Theorems.Thm_Erdos266_two_mul_bigM_lt
-- name    : Erdos266.two_mul_bigM_lt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:40:25.149678+00:00
-- url     : https://prove2.me/theorems/938bfd42-199b-5b05-beeb-c8f0bc3c510e
-- title:
--   Erdos266: two mul big M lt
-- statement:
--   The Erdos266 construction uses the two mul big M lt property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean#L94-L103
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Growth.lean#L94-L103

module
public import Definitions.Def_Erdos266_Defs
public import Definitions.Def_Erdos266_Growth
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.two_mul_bigM_lt {k : ℕ} (hk : 2 ≤ k) : 2 * bigM k < bigN k := by sorry
