-- Prove2me | solution 1 for hasPolychromColouring_mul_unit
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:45:07.040178+00:00
-- url     : https://prove2.me/submissions/4f72f65a-bd7c-45a5-b468-b6c28b7d7aaf

import Definitions.Def_Polychromatic_FourThree_Combi_BlockColour
import Definitions.Def_Polychromatic_FourThree_Combi_CaseOne
import Theorems.Thm_hasPolychromColouring_fin_of_le
import Theorems.Thm_le_polychromNumber
import Theorems.Thm_polychromNumber_iso


set_option autoImplicit true
open Finset Pointwise
variable (m : ℕ)
theorem _root_.solution (u : (ZMod m)ˣ) (S : Finset (ZMod m)) :
    HasPolychromColouring (Fin 3) (S.image (u.val * ·)) ↔
    HasPolychromColouring (Fin 3) S := by
  have key : polychromNumber (S.image (u.val * ·)) = polychromNumber S :=
    polychromNumber_iso (Multiplicative.toAdd (AddAut.mulLeft u))
  exact ⟨fun h => hasPolychromColouring_fin_of_le (by grind) (key ▸ le_polychromNumber h),
    fun h => hasPolychromColouring_fin_of_le (by grind) (key.symm ▸ le_polychromNumber h)⟩
