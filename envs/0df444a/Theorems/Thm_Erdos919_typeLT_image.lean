-- Prove2me | Theorems.Thm_Erdos919_typeLT_image
-- name    : Erdos919.typeLT_image
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:32:59.257432+00:00
-- url     : https://prove2.me/theorems/856ae32a-8598-51d0-87b4-98012fa9558a
-- title:
--   Erdos919: type LT image
-- statement:
--   The Erdos919 construction uses the type LT image property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L736-L740
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L736-L740

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

theorem Erdos919.typeLT_image {A B : Type u} [LinearOrder A] [WellFoundedLT A] [LinearOrder B]
    [WellFoundedLT B] (e : A ≃o B) (X : Set A) : typeLT (e '' X) = typeLT X := by sorry
