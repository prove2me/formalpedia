-- Prove2me | solution 1 for polychromNumber_univ
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:40:39.697732+00:00
-- url     : https://prove2.me/submissions/b90b52fe-7e48-4a2d-8d0c-617214385ee1

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_univ



set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise
theorem _root_.solution [Fintype G] :
    polychromNumber (univ : Finset G) = Fintype.card G := by
  apply le_antisymm
  · exact polychromNumber_le_card
  · exact card_le_polychromNumber hasPolychromColouring_univ
