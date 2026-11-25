-- Prove2me | Theorems.Thm_ErdosPosa_reduction
-- name    : ErdosPosa.reduction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:31:10.608812+00:00
-- url     : https://prove2.me/theorems/c3391472-c58f-53d0-b66a-5d011ad6382a
-- title:
--   Erdos Posa: reduction
-- statement:
--   **Erdős–Pósa, `Cyc` form.**
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMain.lean#L63-L83
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMain.lean#L63-L83

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPPin
public import Definitions.Def_ErdosPosaLib_EPMain
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*}

theorem ErdosPosa.reduction [Finite V] (G : SimpleGraph V) (j : ℕ) :
    (∃ F : Fin (j + 1) → Set V, Pairwise (fun i i' => Disjoint (F i) (F i')) ∧
      ∀ i, Cyc G (F i)) ∨
    ∃ X : Set V, X.ncard ≤ gEP (j + 1) + j ∧ ¬ Cyc G Xᶜ := by sorry
