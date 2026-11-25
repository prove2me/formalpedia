-- Prove2me | Theorems.Thm_Erdos919_bigGraph_smallType
-- name    : Erdos919.bigGraph_smallType
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T18:23:25.903261+00:00
-- url     : https://prove2.me/theorems/3820db03-60fc-552e-bcc8-ba11890a23c3
-- title:
--   Erdos919: big Graph small Type
-- statement:
--   The Erdos919 construction uses the big Graph small Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L491-L516
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L491-L516

module
public import Mathlib
public import Definitions.Def_Erdos919Palomar_Solution
set_option autoImplicit false
@[expose] public section
public section
universe u
open Cardinal Ordinal Set SimpleGraph
open Erdos919
noncomputable section

theorem Erdos919.bigGraph_smallType (H : SimpleGraph W.{u}) (hH : SmallCardCC H) :
    SmallTypeCC (bigGraph H) := by sorry
