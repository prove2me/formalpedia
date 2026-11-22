-- Prove2me | solution 1 for hasPolychromColouring_fin_of_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:44:26.651196+00:00
-- url     : https://prove2.me/submissions/b0296ca2-6c47-4e4f-b2f2-3f28048b59ed

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Theorems.Thm_hasPolychromColouring_of_card_le
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ



set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise
theorem _root_.solution {n : ℕ}
    (hn : n ≠ 0) (hS : n ≤ polychromNumber S) :
    HasPolychromColouring (Fin n) S :=
  hasPolychromColouring_of_card_le (hK := Fin.pos_iff_nonempty.1 (by grind)) <| by simpa
