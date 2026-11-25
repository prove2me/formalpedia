-- Prove2me | Theorems.Thm_Erdos919_smallCard_comap
-- name    : Erdos919.smallCard_comap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:13:43.228602+00:00
-- url     : https://prove2.me/theorems/862506f5-b2d5-4b63-81bb-1f7a885d4016
-- title:
--   Erdos919: small Card comap
-- statement:
--   The Erdos919 construction uses the small Card comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L307-L311
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L307-L311

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

theorem Erdos919.smallCard_comap {V V' : Type u} (e : V ≃ V') {G : SimpleGraph V'}
    (hG : SmallCardCC G) : SmallCardCC (G.comap e) := by sorry
