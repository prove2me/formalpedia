-- Prove2me | solution 1 for polychromNumber_zsmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:45:28.341585+00:00
-- url     : https://prove2.me/submissions/219fb508-2f8a-4041-bed0-537371276a2b

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Theorems.Thm_polychromNumber_image_injective

set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise
theorem _root_.solution [DecidableEq G] [IsAddTorsionFree G] {k : ℤ} (hk : k ≠ 0) :
    polychromNumber (S.image (k • ·)) = polychromNumber S :=
  polychromNumber_image_injective (zsmulAddGroupHom k : G →+ G) (zsmul_right_injective hk)
