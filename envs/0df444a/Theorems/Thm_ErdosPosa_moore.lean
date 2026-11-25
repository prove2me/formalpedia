-- Prove2me | Theorems.Thm_ErdosPosa_moore
-- name    : ErdosPosa.moore
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-25T21:22:35.344059+00:00
-- url     : https://prove2.me/theorems/4e1c87ec-9877-5407-9193-198de736a677
-- title:
--   Erdos Posa: moore
-- statement:
--   **Moore bound.**
--
--   Source: https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMoore.lean#L108-L175
-- source:
--   https://github.com/jtraverso/erdos-posa-cycles/blob/67bfea6b3893ffdf57e76cd83c9c3538647bdec8/ErdosPosaLib/EPMoore.lean#L108-L175

module
public import Mathlib
public import Definitions.Def_ErdosPosaLib_EPCyc
public import Definitions.Def_ErdosPosaLib_EPMoore
set_option autoImplicit true
@[expose] public section
public section
open SimpleGraph
open ErdosPosa
variable {V : Type*} {H : SimpleGraph V}

theorem ErdosPosa.moore [Finite V] (v : V) (r : ℕ) (hdeg : ∀ x, H.Reachable v x → 3 ≤ deg H x)
    (hno : ∀ S : Set V, S.ncard ≤ 2 * r + 1 → ¬ Cyc H S) :
    2 ^ r ≤ {x | H.Reachable v x ∧ H.dist v x = r}.ncard := by sorry
