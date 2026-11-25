-- Prove2me | Theorems.Thm_Erdos919_smallType_comap
-- name    : Erdos919.smallType_comap
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T18:33:15.073591+00:00
-- url     : https://prove2.me/theorems/60ce0a11-98ee-4d7a-a994-babad7ac4551
-- title:
--   Erdos919: small Type comap
-- statement:
--   The Erdos919 construction uses the small Type comap property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L742-L746
-- source:
--   https://github.com/mnn31/erdos-919-palomar/blob/b1aababb75cd555fab236a2217ec8ada6ce047cf/Solution.lean#L742-L746

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

theorem Erdos919.smallType_comap {A B : Type u} [LinearOrder A] [WellFoundedLT A] [LinearOrder B]
    [WellFoundedLT B] (e : A ≃o B) {G : SimpleGraph B} {o : Ordinal.{u}}
    (h : ∀ X : Set B, typeLT X < o → ColorableOn G X ℕ) :
    ∀ Y : Set A, typeLT Y < o → ColorableOn (G.comap e) Y ℕ := by sorry
