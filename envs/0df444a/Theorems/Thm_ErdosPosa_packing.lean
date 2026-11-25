-- Prove2me | Theorems.Thm_ErdosPosa_packing
-- name    : ErdosPosa.packing
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-25T21:29:44.790621+00:00
-- url     : https://prove2.me/theorems/df71e6a9-dbce-4727-ada9-285c2fe3ae9c
-- title:
--   Erdos Posa: packing
-- statement:
--   **Packing lemma.**
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L304-L364
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPPacking.lean#L304-L364

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

theorem ErdosPosa.packing [Fintype V] (g : ℕ → ℕ)
    (hg : ∀ k, (g k : ℤ) + 2 * (2 * Nat.log 2 (g (k + 1) + 1) + 3) ≤ g (k + 1)) :
    ∀ (k : ℕ) (H : SimpleGraph V), (∀ v, deg H v ≤ 3) → (g k : ℤ) ≤ psi H →
      ∃ T : Fin k → Set V, Pairwise (fun i j => Disjoint (T i) (T j)) ∧ ∀ i, Cyc H (T i) := by sorry
