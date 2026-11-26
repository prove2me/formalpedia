-- Prove2me | Theorems.Thm_DenseTriangleFree_enumIndep_sound
-- name    : DenseTriangleFree.enumIndep_sound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T22:46:32.385025+00:00
-- url     : https://prove2.me/theorems/acd70df9-1a6f-5aef-a82c-70845f9a0907
-- title:
--   Dense Triangle Free: enum Indep sound
-- statement:
--   The Dense Triangle Free construction uses the enum Indep sound property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Heavy.lean#L35-L63
-- source:
--   https://github.com/jtraverso/jin-triangle-free/blob/ae47df0ddb29c58a71afed658f9bf74aef1b6e90/JinLib/Heavy.lean#L35-L63

module
public import Mathlib
public import Definitions.Def_JinLib_Grotzsch
public import Definitions.Def_JinLib_Heavy
set_option autoImplicit true
@[expose] public section
public section
open DenseTriangleFree
open SimpleGraph

theorem DenseTriangleFree.enumIndep_sound (E : ℕ → ℕ → Bool) (P : List ℕ → Bool)
    (hP : ∀ l l' : List ℕ, l.Perm l' → P l = P l') (q : ℕ → Prop) [DecidablePred q]
    (hq : ∀ i j, q i → q j → E i j = false) :
    ∀ vs ch : List ℕ, (∀ j ∈ ch, q j) → enumIndep E P vs ch = true →
      P (vs.filter (fun i => decide (q i)) ++ ch) = true := by sorry
