-- Prove2me | solution 1 for le_polychromNumber_iff_hasPolychromColouring
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:45:03.664034+00:00
-- url     : https://prove2.me/submissions/a21b50fe-2173-48be-9997-fc70059f74b0

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Theorems.Thm_le_polychromNumber
import Theorems.Thm_hasPolychromColouring_fin_of_le

set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise
theorem _root_.solution {n : ℕ} (hn : n ≠ 0) {S : Finset G} :
    n ≤ polychromNumber S ↔ HasPolychromColouring (Fin n) S := by
  constructor
  · exact hasPolychromColouring_fin_of_le hn
  · exact le_polychromNumber
