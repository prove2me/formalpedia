-- Prove2me | solution 1 for polychromNumber_nsmul
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:53:48.826897+00:00
-- url     : https://prove2.me/submissions/0b77dbfd-7c7e-43a7-8270-1f55d05b2c94

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Theorems.Thm_polychromNumber_image_injective

set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise
theorem _root_.solution [DecidableEq G] [IsAddTorsionFree G] {k : ℕ} (hk : k ≠ 0) :
    polychromNumber (S.image (k • ·)) = polychromNumber S :=
  polychromNumber_image_injective (nsmulAddMonoidHom k : G →+ G) (nsmul_right_injective hk)
