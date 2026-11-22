-- Prove2me | solution 1 for lt_straussFunction_of_not_hasPolychromColouring
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-21T08:52:51.049183+00:00
-- url     : https://prove2.me/submissions/f28adffb-36f0-44d4-adf9-18cc91a07656

import Definitions.Def_Polychromatic_Existence
import Definitions.Def_Polychromatic_PolychromNumber
import Definitions.Def_Polychromatic_LovaszFunction
import Theorems.Thm_straussFunction_spec

set_option autoImplicit true
open Finset
theorem _root_.solution {k : ℕ} (hk : k ≠ 0) {S : Finset ℤ}
    (hkS : ¬ HasPolychromColouring (Fin k) S) :
    #S < straussFunction k := by
  by_contra!
  exact hkS (straussFunction_spec hk S this)
