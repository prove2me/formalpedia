-- Prove2me | solution 1 for polychromNumber_pos
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:53:42.786432+00:00
-- url     : https://prove2.me/submissions/34e89e76-8231-469f-8bcf-54f087eaa175

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Theorems.Thm_one_le_polychromNumber

set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise
theorem _root_.solution (hS : S.Nonempty) : 0 < polychromNumber S :=
  one_le_polychromNumber hS
