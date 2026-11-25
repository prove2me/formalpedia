-- Prove2me | Theorems.Thm_ErdosPosa_pairwise_disjoint_cons
-- name    : ErdosPosa.pairwise_disjoint_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:28:30.143551+00:00
-- url     : https://prove2.me/theorems/3ffb5a9d-a0da-5a08-b7f2-5a474eaef02d
-- title:
--   Erdos Posa: pairwise disjoint cons
-- statement:
--   The Erdos Posa construction uses the pairwise disjoint cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L272-L287
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L272-L287

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPShort
public import Definitions.Def_ErdosPosaLib_EPPacking
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}

theorem ErdosPosa.pairwise_disjoint_cons {k : ℕ} (X : Set V) (F : Fin k → Set V)
    (hF : Pairwise (fun i j => Disjoint (F i) (F j))) (hX : ∀ i, Disjoint X (F i)) :
    Pairwise (fun i j => Disjoint ((Fin.cons X F : Fin (k + 1) → Set V) i)
      ((Fin.cons X F : Fin (k + 1) → Set V) j)) := by sorry
