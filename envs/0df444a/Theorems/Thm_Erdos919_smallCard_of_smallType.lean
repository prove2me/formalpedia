-- Prove2me | Theorems.Thm_Erdos919_smallCard_of_smallType
-- name    : Erdos919.smallCard_of_smallType
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:24:00.830345+00:00
-- url     : https://prove2.me/theorems/5310551f-9721-441b-9d8b-f17dfd1f69b5
-- title:
--   Erdos919: small Card of small Type
-- statement:
--   The Erdos919 construction uses the small Card of small Type property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L518-L526
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L518-L526

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

theorem Erdos919.smallCard_of_smallType {G : SimpleGraph (W.{u} ×ₗ W.{u})} (hG : SmallTypeCC G) :
    SmallCardCC G := by sorry
