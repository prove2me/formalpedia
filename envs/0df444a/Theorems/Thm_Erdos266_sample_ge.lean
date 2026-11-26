-- Prove2me | Theorems.Thm_Erdos266_sample_ge
-- name    : Erdos266.sample_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T02:47:21.343032+00:00
-- url     : https://prove2.me/theorems/44c71697-860f-5d61-af05-aa7abb301152
-- title:
--   Erdos266: sample ge
-- statement:
--   The Erdos266 construction uses the sample ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Algorithm.lean#L199-L201
-- source:
--   https://github.com/benkeene/erdos266/blob/ef01b23804a60669f24b25733f1a2b688084609d/Erdos266/Algorithm.lean#L199-L201

module
public import Definitions.Def_Erdos266_LatticeLemma
public import Definitions.Def_Erdos266_Growth
public import Definitions.Def_Erdos266_Algorithm
set_option autoImplicit false
@[expose] public section
public section
open Erdos266
open Finset

theorem Erdos266.sample_ge {j l : ℕ} : (bigN l : ℝ) ≤ (((j + 1) * bigN l : ℕ) : ℝ) := by sorry
