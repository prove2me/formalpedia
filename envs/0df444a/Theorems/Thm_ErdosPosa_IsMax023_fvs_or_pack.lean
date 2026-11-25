-- Prove2me | Theorems.Thm_ErdosPosa_IsMax023_fvs_or_pack
-- name    : ErdosPosa.IsMax023.fvs_or_pack
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:31:00.734595+00:00
-- url     : https://prove2.me/theorems/6d647c77-1144-4067-be01-88158403486f
-- title:
--   Is Max023: fvs or pack
-- statement:
--   Either `j + 1` disjoint cycles, or at most `j` vertices meeting all cycles inside `A`.
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPin.lean#L296-L343
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPin.lean#L296-L343

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPMaximal
public import Definitions.Def_ErdosPosaLib_EPPin
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}
variable [Finite V] {G H : SimpleGraph V}

theorem ErdosPosa.IsMax023.fvs_or_pack (hH : IsMax023 G H) : ∀ (j : ℕ) (A : Set V),
    (∀ v ∈ A, deg H v ≠ 3) →
    (∃ F : Fin (j + 1) → Set V, Pairwise (fun i i' => Disjoint (F i) (F i')) ∧
      (∀ i, F i ⊆ A) ∧ ∀ i, Cyc G (F i)) ∨
    ∃ Z : Finset V, Z.card ≤ j ∧ ¬ Cyc G (A \ ↑Z) := by sorry
