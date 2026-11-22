-- Prove2me | solution 1 for hasPolychromColouring_of_card_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:43:47.937871+00:00
-- url     : https://prove2.me/submissions/825445bb-6d3d-411c-9bd3-708384ee359f

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Theorems.Thm_HasPolychromColouring_of_injective
import Theorems.Thm_hasPolychromColouring_neg
import Theorems.Thm_hasPolychromColouring_univ
attribute [local simp] hasPolychromColouring_neg
attribute [local simp] hasPolychromColouring_univ



set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise
theorem _root_.solution [Fintype K] [hK : Nonempty K]
    (hK : card K ≤ polychromNumber S) :
    HasPolychromColouring K S := by
  have hS : S.Nonempty := by
    rw [nonempty_iff_ne_empty]
    rintro rfl
    simp at hK
  exact .of_injective (hasPolychromColouring_fin hS)
    (((equivFin K).toEmbedding.trans (Fin.castLEEmb hK)).injective)
