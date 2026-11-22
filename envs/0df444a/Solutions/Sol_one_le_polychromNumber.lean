-- Prove2me | solution 1 for one_le_polychromNumber
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:41:29.1337+00:00
-- url     : https://prove2.me/submissions/4b8e7543-d64d-42fd-99df-c484d6edef64

import Definitions.Def_Polychromatic_Colouring
import Definitions.Def_Polychromatic_PolychromNumber
import Theorems.Thm_le_polychromNumber
import Theorems.Thm_hasPolychromColouring_subsingleton


set_option autoImplicit true
variable {G : Type*} [AddCommGroup G] {S : Finset G} {K : Type*}
open Finset Fintype Pointwise
theorem _root_.solution (hS : S.Nonempty) : 1 ≤ polychromNumber S :=
  le_polychromNumber (hasPolychromColouring_subsingleton hS)
